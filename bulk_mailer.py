#!/usr/bin/env python3
"""
Bulk Mailer - A Tkinter desktop app for managing a mailing list and sending
bulk HTML/plain-text emails with attachments, batching, scheduling and a
sent-flag tracking system.

Single-file application. See requirements.txt for dependencies.
"""

import os
import re
import csv
import json
import sys
import time
import difflib
import smtplib
import logging
import threading
import mimetypes
from datetime import datetime, timedelta
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from email.mime.base import MIMEBase
from email import encoders

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog

try:
    import schedule  # optional - falls back to threading.Timer if missing
    HAS_SCHEDULE = True
except ImportError:
    HAS_SCHEDULE = False

# ----------------------------------------------------------------------------
# Constants & Paths
# ----------------------------------------------------------------------------

if getattr(sys, "frozen", False):
    # Running as a PyInstaller-built executable: __file__ points into a
    # temporary extraction folder that's wiped on exit, so store data next
    # to the actual executable instead or it would appear to "disappear"
    # between runs.
    APP_DIR = os.path.dirname(os.path.abspath(sys.executable))
else:
    try:
        APP_DIR = os.path.dirname(os.path.abspath(__file__))
    except NameError:
        # __file__ isn't defined when running inside Jupyter/IPython cells or
        # an interactive REPL - fall back to the current working directory.
        APP_DIR = os.path.abspath(os.getcwd())
EMAILS_FILE = os.path.join(APP_DIR, "emails.json")
LOG_FILE = os.path.join(APP_DIR, "bulk_mailer.log")
SCHEDULE_FILE = os.path.join(APP_DIR, "scheduled_jobs.json")

EMAIL_REGEX = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]+$")

PROVIDERS = {
    "Gmail":            {"server": "smtp.gmail.com",        "port": 587, "tls": True,  "ssl": False},
    "Outlook/Office365": {"server": "smtp.office365.com",     "port": 587, "tls": True,  "ssl": False},
    "Yahoo":            {"server": "smtp.mail.yahoo.com",    "port": 587, "tls": True,  "ssl": False},
    "Custom SMTP":      {"server": "",                        "port": 587, "tls": True,  "ssl": False},
}

# ----------------------------------------------------------------------------
# "Sunset" theme: palette + small gradient/animation helpers
# ----------------------------------------------------------------------------

SUNSET_STOPS = [
    (255, 255, 255),  # white
    (219, 234, 254),  # pale blue
]

HERO_STOPS = [
    (12, 24, 58),      # deep navy
    (29, 65, 148),     # rich blue
    (37, 99, 235),     # accent blue
    (96, 165, 250),    # light sky blue
]

PANEL_BG      = "#ffffff"   # card / frame background
PANEL_BG_2    = "#eef2f8"   # slightly tinted panel (tab strip, header, status bar)
ROW_BG        = "#ffffff"   # treeview row background
ROW_ALT_BG    = "#f5f8fc"
SENT_ROW_BG   = "#dbeafe"   # light blue tint for "sent" rows
INPUT_BG      = "#ffffff"
TEXT_LIGHT    = "#1a2233"   # primary text (dark, for the light background)
TEXT_MUTED    = "#5b6472"   # secondary/muted text
ACCENT_CORAL  = "#2563eb"   # primary blue accent
ACCENT_GOLD   = "#3b82f6"   # lighter blue, used for hover states
ACCENT_PINK   = "#1d4ed8"   # darker blue, used for pressed states
ACCENT_DEEP   = "#d7dee8"   # neutral light border/outline color

SIDEBAR_BG        = "#0f1f3d"   # dark navy sidebar
SIDEBAR_BG_HOVER  = "#16305e"
SIDEBAR_TEXT      = "#c3d3f0"
SIDEBAR_TEXT_DIM  = "#7c8db3"
SIDEBAR_ACTIVE_BG = "#2563eb"


def _lerp(a, b, t):
    return a + (b - a) * t


def _lerp_color(c1, c2, t):
    return tuple(int(round(_lerp(c1[i], c2[i], t))) for i in range(3))


def _rgb_to_hex(rgb):
    return "#%02x%02x%02x" % tuple(max(0, min(255, v)) for v in rgb)


def sunset_color_at(fraction, stops=None, phase=0.0):
    """Return a hex color sampled along the multi-stop sunset gradient.
    `fraction` is 0..1 along the gradient axis. `phase` slowly rotates which
    stop sits at fraction=0, used to animate the gradient over time."""
    stops = stops or SUNSET_STOPS
    n = len(stops)
    pos = (fraction + phase) % 1.0
    scaled = pos * n
    i = int(scaled) % n
    j = (i + 1) % n
    t = scaled - int(scaled)
    return _rgb_to_hex(_lerp_color(stops[i], stops[j], t))


# ----------------------------------------------------------------------------
# Logging setup (file + GUI panel via a custom handler)
# ----------------------------------------------------------------------------

logger = logging.getLogger("bulk_mailer")
logger.setLevel(logging.DEBUG)
file_handler = logging.FileHandler(LOG_FILE, encoding="utf-8")
file_handler.setFormatter(logging.Formatter("%(asctime)s [%(levelname)s] %(message)s"))
logger.addHandler(file_handler)


class GuiLogHandler(logging.Handler):
    """Routes log records into a Tkinter Text widget (thread-safe via .after)."""

    def __init__(self, text_widget):
        super().__init__()
        self.text_widget = text_widget

    def emit(self, record):
        msg = self.format(record)

        def append():
            self.text_widget.configure(state="normal")
            self.text_widget.insert("end", msg + "\n")
            self.text_widget.see("end")
            self.text_widget.configure(state="disabled")

        try:
            self.text_widget.after(0, append)
        except RuntimeError:
            pass


# ----------------------------------------------------------------------------
# Data model: Mailing list persistence
# ----------------------------------------------------------------------------

class MailingList:
    """Holds recipient records: {name, email, attachment_path, date_added, sent, last_sent}."""

    def __init__(self, path=EMAILS_FILE):
        self.path = path
        self.records = []
        self.load()

    def load(self):
        if os.path.exists(self.path):
            try:
                with open(self.path, "r", encoding="utf-8") as f:
                    self.records = json.load(f)
            except (json.JSONDecodeError, OSError) as e:
                logger.error(f"Failed to load mailing list: {e}")
                self.records = []
        else:
            self.records = []

    def save(self):
        try:
            with open(self.path, "w", encoding="utf-8") as f:
                json.dump(self.records, f, indent=2)
        except OSError as e:
            logger.error(f"Failed to save mailing list: {e}")

    def add(self, email, name="", attachment_path=""):
        email = email.strip()
        name = name.strip()
        attachment_path = (attachment_path or "").strip()
        if not EMAIL_REGEX.match(email):
            return False, f"Invalid email format: {email}"
        if any(r["email"].lower() == email.lower() for r in self.records):
            return False, f"Duplicate email skipped: {email}"
        self.records.append({
            "name": name,
            "email": email,
            "attachment_path": attachment_path,
            "date_added": datetime.now().isoformat(timespec="seconds"),
            "sent": False,
            "last_sent": None,
        })
        self.save()
        return True, "OK"

    def set_attachment(self, email, path):
        """Set the per-recipient attachment for a specific email."""
        for r in self.records:
            if r["email"].lower() == email.lower():
                r["attachment_path"] = path.strip()
        self.save()

    def add_raw_line(self, line):
        """Parses email, email|name, or email|name|attachment_path format."""
        line = line.strip()
        if not line:
            return False, "Empty line"
        parts = line.split("|")
        email = parts[0]
        name = parts[1] if len(parts) > 1 else ""
        attachment_path = parts[2] if len(parts) > 2 else ""
        return self.add(email, name, attachment_path)

    def remove(self, emails):
        emails_lower = {e.lower() for e in emails}
        before = len(self.records)
        self.records = [r for r in self.records if r["email"].lower() not in emails_lower]
        self.save()
        return before - len(self.records)

    def mark_sent(self, email):
        for r in self.records:
            if r["email"].lower() == email.lower():
                r["sent"] = True
                r["last_sent"] = datetime.now().isoformat(timespec="seconds")
        self.save()

    def reset_sent_flags(self, emails=None):
        for r in self.records:
            if emails is None or r["email"] in emails:
                r["sent"] = False
                r["last_sent"] = None
        self.save()

    def import_csv(self, path):
        added, skipped = 0, 0
        with open(path, "r", encoding="utf-8-sig", newline="") as f:
            reader = csv.DictReader(f)
            fieldmap = {k.lower().strip(): k for k in (reader.fieldnames or [])}
            email_key = fieldmap.get("email")
            name_key  = fieldmap.get("name")
            attach_key = fieldmap.get("attachment_path") or fieldmap.get("attachment")
            if not email_key:
                raise ValueError("CSV must contain an 'email' column")
            for row in reader:
                email = row.get(email_key, "")
                name  = row.get(name_key, "") if name_key else ""
                attachment_path = row.get(attach_key, "") if attach_key else ""
                ok, _ = self.add(email, name, attachment_path)
                added += int(ok)
                skipped += int(not ok)
        return added, skipped

    def export_csv(self, path):
        with open(path, "w", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["name", "email", "attachment_path",
                             "date_added", "sent", "last_sent"])
            for r in self.records:
                writer.writerow([r.get("name",""), r["email"],
                                  r.get("attachment_path",""),
                                  r["date_added"], r["sent"],
                                  r["last_sent"] or ""])

    def sort_by(self, key):
        if key == "domain":
            self.records.sort(key=lambda r: r["email"].split("@")[-1].lower())
        elif key == "email":
            self.records.sort(key=lambda r: r["email"].lower())
        elif key == "name":
            self.records.sort(key=lambda r: r["name"].lower())
        elif key == "date":
            self.records.sort(key=lambda r: r["date_added"])
        elif key == "sent":
            self.records.sort(key=lambda r: r["sent"])
        self.save()


# ----------------------------------------------------------------------------
# Email sending engine
# ----------------------------------------------------------------------------

class SmtpCredentials:
    def __init__(self, server, port, use_tls, use_ssl, username, password, from_addr=None):
        self.server = server
        self.port = int(port)
        self.use_tls = use_tls
        self.use_ssl = use_ssl
        self.username = username
        self.password = password
        self.from_addr = from_addr or username


def build_message(creds, to_addr, subject, body, is_html, attachments):
    msg = MIMEMultipart("mixed")
    msg["From"] = creds.from_addr
    msg["To"] = to_addr
    msg["Subject"] = subject

    body_part = MIMEMultipart("alternative")
    if is_html:
        body_part.attach(MIMEText(body, "html"))
    else:
        body_part.attach(MIMEText(body, "plain"))
    msg.attach(body_part)

    for path in attachments:
        if not os.path.isfile(path):
            logger.warning(f"Attachment missing, skipping: {path}")
            continue
        ctype, _ = mimetypes.guess_type(path)
        maintype, subtype = (ctype or "application/octet-stream").split("/", 1)
        with open(path, "rb") as f:
            part = MIMEBase(maintype, subtype)
            part.set_payload(f.read())
        encoders.encode_base64(part)
        part.add_header("Content-Disposition", "attachment",
                         filename=os.path.basename(path))
        msg.attach(part)

    return msg


class EmailSender:
    """Handles SMTP connection + batched sending with rate limiting."""

    def __init__(self, creds: SmtpCredentials):
        self.creds = creds
        self._conn = None

    def connect(self):
        if self.creds.use_ssl:
            self._conn = smtplib.SMTP_SSL(self.creds.server, self.creds.port, timeout=30)
        else:
            self._conn = smtplib.SMTP(self.creds.server, self.creds.port, timeout=30)
            if self.creds.use_tls:
                self._conn.starttls()
        self._conn.login(self.creds.username, self.creds.password)
        logger.info(f"Connected to {self.creds.server}:{self.creds.port}")

    def disconnect(self):
        if self._conn:
            try:
                self._conn.quit()
            except Exception:
                pass
            self._conn = None

    def send_one(self, to_addr, subject, body, is_html, attachments):
        msg = build_message(self.creds, to_addr, subject, body, is_html, attachments)
        self._conn.sendmail(self.creds.from_addr, [to_addr], msg.as_string())

    def send_batches(self, recipients, subject, body, is_html, attachments,
                      batch_size, delay_seconds, mailing_list: MailingList,
                      progress_cb=None, stop_flag=None, dry_run=False):
        """
        recipients: list of dicts with 'email'/'name'
        progress_cb(done, total, current_email, success)
        stop_flag: callable returning True if user requested cancel
        """
        total = len(recipients)
        done = 0
        sent_count = 0
        failed = []

        if not dry_run:
            self.connect()

        try:
            for batch_start in range(0, total, batch_size):
                if stop_flag and stop_flag():
                    logger.info("Sending cancelled by user.")
                    break

                batch = recipients[batch_start:batch_start + batch_size]
                logger.info(f"Processing batch {batch_start // batch_size + 1} "
                            f"({len(batch)} recipients)")

                for rec in batch:
                    if stop_flag and stop_flag():
                        logger.info("Sending cancelled by user.")
                        break
                    addr = rec["email"]
                    personalized = body.replace("{{name}}", rec.get("name") or "")

                    # Merge global attachments with this recipient's personal file
                    rec_attach = rec.get("attachment_path", "").strip()
                    effective_attachments = list(attachments)
                    if rec_attach and os.path.isfile(rec_attach):
                        effective_attachments.append(rec_attach)
                    elif rec_attach and not os.path.isfile(rec_attach):
                        logger.warning(f"Per-recipient file not found for {addr}: {rec_attach}")

                    try:
                        if dry_run:
                            attach_note = f" + {os.path.basename(rec_attach)}" if rec_attach else ""
                            logger.info(f"[DRY RUN] Would send to {addr}{attach_note}")
                        else:
                            self.send_one(addr, subject, personalized, is_html, effective_attachments)
                            mailing_list.mark_sent(addr)
                            logger.info(f"Sent to {addr}" +
                                        (f" (+ {os.path.basename(rec_attach)})" if rec_attach else ""))
                        sent_count += 1
                    except Exception as e:
                        logger.error(f"Failed to send to {addr}: {e}")
                        failed.append(addr)
                    done += 1
                    if progress_cb:
                        progress_cb(done, total, addr, addr not in failed)

                # Rate limit delay between batches (not after the very last batch)
                if batch_start + batch_size < total and delay_seconds > 0:
                    time.sleep(delay_seconds)
        finally:
            if not dry_run:
                self.disconnect()

        return sent_count, failed


# ----------------------------------------------------------------------------
# Scheduler (simple file-persisted, in-process)
# ----------------------------------------------------------------------------

class JobScheduler:
    """
    Lightweight scheduler: stores pending jobs to SCHEDULE_FILE so they survive
    an app restart (the app must be running again before the target time for
    the job to actually fire - this is documented as a limitation).
    """

    def __init__(self, on_fire):
        self.on_fire = on_fire
        self._timers = {}
        self._load()

    def _load(self):
        self.jobs = []
        if os.path.exists(SCHEDULE_FILE):
            try:
                with open(SCHEDULE_FILE, "r", encoding="utf-8") as f:
                    self.jobs = json.load(f)
            except (OSError, json.JSONDecodeError):
                self.jobs = []

    def _save(self):
        with open(SCHEDULE_FILE, "w", encoding="utf-8") as f:
            json.dump(self.jobs, f, indent=2)

    def schedule_job(self, run_at: datetime, job_payload: dict):
        job_id = str(int(time.time() * 1000))
        job = {"id": job_id, "run_at": run_at.isoformat(), "payload": job_payload,
               "fired": False}
        self.jobs.append(job)
        self._save()
        self._arm(job)
        return job_id

    def _arm(self, job):
        run_at = datetime.fromisoformat(job["run_at"])
        delay = max(0, (run_at - datetime.now()).total_seconds())
        t = threading.Timer(delay, self._fire, args=(job["id"],))
        t.daemon = True
        self._timers[job["id"]] = t
        t.start()
        logger.info(f"Scheduled job {job['id']} to run at {run_at} "
                     f"({delay:.0f}s from now)")

    def rearm_pending(self):
        """Call on app startup to re-arm any jobs whose time hasn't passed."""
        now = datetime.now()
        for job in self.jobs:
            if job["fired"]:
                continue
            run_at = datetime.fromisoformat(job["run_at"])
            if run_at <= now:
                # Missed while app was closed - fire immediately, flagged.
                logger.warning(f"Job {job['id']} missed its scheduled time; "
                                f"running now.")
                self._fire(job["id"])
            else:
                self._arm(job)

    def _fire(self, job_id):
        job = next((j for j in self.jobs if j["id"] == job_id), None)
        if not job or job["fired"]:
            return
        job["fired"] = True
        self._save()
        try:
            self.on_fire(job["payload"])
        except Exception as e:
            logger.error(f"Scheduled job {job_id} failed: {e}")

    def cancel(self, job_id):
        t = self._timers.pop(job_id, None)
        if t:
            t.cancel()
        for j in self.jobs:
            if j["id"] == job_id:
                j["fired"] = True
        self._save()


# ----------------------------------------------------------------------------
# GUI Application
# ----------------------------------------------------------------------------

class BulkMailerApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Bulk Mailer")
        self.root.geometry("1080x720")
        self.root.configure(bg=PANEL_BG)

        self.mailing_list = MailingList()
        self.attachments = []
        self.send_thread = None
        self.cancel_requested = False
        self.current_page = None
        self._pending_login = None
        self._login_anim_job = None
        self._login_gradient_phase = 0.0

        self._setup_style()
        self._build_login_page()
        self._build_app_shell()

        self.scheduler = JobScheduler(self._run_scheduled_job)
        self.scheduler.rearm_pending()

        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

        # Show the login page first; the app shell stays built but hidden
        # until the person logs in or chooses to skip.
        self.login_frame.pack(fill="both", expand=True)
        self.root.update_idletasks()
        self._draw_login_background()
        self._start_login_animation()

    # ---------------- Theme ----------------

    def _setup_style(self):
        style = ttk.Style(self.root)
        try:
            style.theme_use("clam")
        except Exception:
            pass

        style.configure(".", background=PANEL_BG, foreground=TEXT_LIGHT,
                         fieldbackground=INPUT_BG, bordercolor=PANEL_BG_2,
                         font=("Segoe UI", 10))

        style.configure("TFrame", background=PANEL_BG)
        style.configure("Panel.TFrame", background=PANEL_BG)
        style.configure("TLabel", background=PANEL_BG, foreground=TEXT_LIGHT)
        style.configure("Status.TLabel", background=PANEL_BG_2, foreground=TEXT_MUTED,
                         padding=(8, 4))

        style.configure("TLabelframe", background=PANEL_BG, bordercolor=ACCENT_DEEP,
                         borderwidth=1, relief="solid")
        style.configure("TLabelframe.Label", background=PANEL_BG, foreground=TEXT_MUTED,
                         font=("Segoe UI", 9, "bold"))

        style.configure("TButton", background=ACCENT_CORAL, foreground="#ffffff",
                         borderwidth=0, padding=(9, 5), font=("Segoe UI", 9))
        style.map("TButton",
                  background=[("active", ACCENT_GOLD), ("pressed", ACCENT_PINK),
                              ("disabled", PANEL_BG_2)],
                  foreground=[("disabled", TEXT_MUTED)])

        style.configure("TEntry", fieldbackground=INPUT_BG, foreground=TEXT_LIGHT,
                         insertcolor=TEXT_LIGHT, bordercolor=ACCENT_DEEP, borderwidth=1)
        style.configure("TCombobox", fieldbackground=INPUT_BG, foreground=TEXT_LIGHT,
                         background=INPUT_BG, arrowcolor=TEXT_MUTED)
        style.map("TCombobox", fieldbackground=[("readonly", INPUT_BG)],
                  foreground=[("readonly", TEXT_LIGHT)])

        style.configure("TCheckbutton", background=PANEL_BG, foreground=TEXT_LIGHT)
        style.configure("TRadiobutton", background=PANEL_BG, foreground=TEXT_LIGHT)
        style.map("TRadiobutton", foreground=[("selected", ACCENT_CORAL)])
        style.map("TCheckbutton", foreground=[("selected", ACCENT_CORAL)])

        style.configure("Treeview", background=ROW_BG, fieldbackground=ROW_BG,
                        foreground=TEXT_LIGHT, borderwidth=0, rowheight=24)
        style.configure("Treeview.Heading", background=PANEL_BG_2, foreground=TEXT_LIGHT,
                        font=("Segoe UI", 9, "bold"), relief="flat")
        style.map("Treeview.Heading", background=[("active", ACCENT_DEEP)])
        style.map("Treeview", background=[("selected", ACCENT_CORAL)],
                  foreground=[("selected", "#ffffff")])

        style.configure("TScrollbar", background=PANEL_BG_2, troughcolor=PANEL_BG,
                        arrowcolor=TEXT_MUTED, bordercolor=PANEL_BG)

        style.configure("TProgressbar", troughcolor=PANEL_BG_2, background=ACCENT_CORAL,
                        bordercolor=PANEL_BG, lightcolor=ACCENT_CORAL, darkcolor=ACCENT_CORAL)

        style.configure("TMenubutton", background=PANEL_BG_2, foreground=TEXT_LIGHT)

    # ---------------- Login page ----------------

    def _build_login_page(self):
        self.login_frame = tk.Frame(self.root, bg=PANEL_BG)

        self.login_canvas = tk.Canvas(self.login_frame, highlightthickness=0, bd=0)
        self.login_canvas.pack(fill="both", expand=True)
        self.login_canvas.bind("<Configure>", lambda e: self._draw_login_background())

        card = tk.Frame(self.login_canvas, bg=PANEL_BG, padx=44, pady=38,
                         highlightthickness=1, highlightbackground=ACCENT_DEEP)
        self._login_card_window = self.login_canvas.create_window(0, 0, window=card, anchor="center")
        self.login_card = card

        tk.Label(card, text="Bulk Mailer", font=("Segoe UI", 22, "bold"),
                 bg=PANEL_BG, fg=TEXT_LIGHT).pack(pady=(0, 2))
        tk.Label(card, text="Sign in to send your campaigns", font=("Segoe UI", 10),
                 bg=PANEL_BG, fg=TEXT_MUTED).pack(pady=(0, 22))

        ttk.Label(card, text="Email").pack(anchor="w")
        self.login_email_var = tk.StringVar()
        ttk.Entry(card, textvariable=self.login_email_var, width=34).pack(pady=(2, 12))

        ttk.Label(card, text="Password").pack(anchor="w")
        self.login_password_var = tk.StringVar()
        ttk.Entry(card, textvariable=self.login_password_var, show="*", width=34).pack(pady=(2, 12))

        ttk.Label(card, text="Provider").pack(anchor="w")
        self.login_provider_var = tk.StringVar(value="Gmail")
        ttk.Combobox(card, textvariable=self.login_provider_var,
                     values=list(PROVIDERS.keys()), state="readonly", width=31).pack(pady=(2, 16))

        self.remember_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(card, text="Remember these details for this session",
                         variable=self.remember_var).pack(anchor="w", pady=(0, 18))

        ttk.Button(card, text="Log In", command=self._do_login).pack(fill="x", pady=(0, 10))

        skip = tk.Label(card, text="Continue without logging in", bg=PANEL_BG, fg=ACCENT_CORAL,
                         font=("Segoe UI", 9, "underline"), cursor="hand2")
        skip.pack()
        skip.bind("<Button-1>", lambda e: self._skip_login())

    def _draw_login_background(self):
        c = self.login_canvas
        w = max(c.winfo_width(), 1)
        h = max(c.winfo_height(), 1)
        c.delete("grad")
        bands = 40
        band_h = max(1, h // bands)
        for i in range(bands + 1):
            frac = i / bands
            color = sunset_color_at(frac, stops=HERO_STOPS, phase=self._login_gradient_phase)
            y0 = i * band_h
            c.create_rectangle(0, y0, w, y0 + band_h + 1, fill=color, outline=color, tags="grad")
        c.tag_lower("grad")
        c.coords(self._login_card_window, w / 2, h / 2)

    def _start_login_animation(self):
        def tick():
            if not self.login_frame.winfo_ismapped():
                self._login_anim_job = None
                return
            self._login_gradient_phase = (self._login_gradient_phase + 0.001) % 1.0
            self._draw_login_background()
            self._login_anim_job = self.root.after(100, tick)
        if self._login_anim_job is None:
            tick()

    def _stop_login_animation(self):
        if self._login_anim_job is not None:
            try:
                self.root.after_cancel(self._login_anim_job)
            except Exception:
                pass
            self._login_anim_job = None

    def _do_login(self):
        email = self.login_email_var.get().strip()
        if email and not EMAIL_REGEX.match(email):
            messagebox.showwarning("Log In", "That doesn't look like a valid email address.")
            return
        if self.remember_var.get():
            self._pending_login = {
                "email": email,
                "password": self.login_password_var.get(),
                "provider": self.login_provider_var.get(),
            }
        else:
            self._pending_login = None
        self._enter_app()

    def _skip_login(self):
        self._pending_login = None
        self._enter_app()

    def _enter_app(self):
        self._stop_login_animation()
        self.login_frame.pack_forget()
        self.app_shell.pack(fill="both", expand=True)

        if self._pending_login:
            info = self._pending_login
            if info["email"]:
                self.username_entry.delete(0, "end")
                self.username_entry.insert(0, info["email"])
            if info["password"]:
                self.password_entry.delete(0, "end")
                self.password_entry.insert(0, info["password"])
            if info["provider"] in PROVIDERS:
                self.provider_var.set(info["provider"])
                self._on_provider_change()

        self.show_page("welcome", animate=False)

    def _logout(self):
        if not messagebox.askyesno("Log Out", "Return to the login screen?"):
            return
        self.app_shell.pack_forget()
        self.login_password_var.set("")
        self.login_frame.pack(fill="both", expand=True)
        self.root.update_idletasks()
        self._draw_login_background()
        self._start_login_animation()

    # ---------------- App shell: sidebar + pages ----------------

    def _build_app_shell(self):
        self.app_shell = ttk.Frame(self.root, style="Panel.TFrame")
        # Not packed yet - shown only after login/skip.

        self.status_var = tk.StringVar(value="Ready")
        status_bar = ttk.Label(self.app_shell, textvariable=self.status_var,
                                style="Status.TLabel", anchor="w")
        status_bar.pack(fill="x", side="bottom")

        body = ttk.Frame(self.app_shell, style="Panel.TFrame")
        body.pack(fill="both", expand=True)

        sidebar = tk.Frame(body, bg=SIDEBAR_BG, width=200)
        sidebar.pack(side="left", fill="y")
        sidebar.pack_propagate(False)
        self._build_sidebar(sidebar)

        content_outer = ttk.Frame(body, style="Panel.TFrame")
        content_outer.pack(side="left", fill="both", expand=True)

        self.content_header_var = tk.StringVar(value="Welcome")
        ttk.Label(content_outer, textvariable=self.content_header_var,
                  font=("Segoe UI", 14, "bold")).pack(fill="x", padx=18, pady=(16, 6), anchor="w")

        self.page_container = ttk.Frame(content_outer, style="Panel.TFrame")
        self.page_container.pack(fill="both", expand=True, padx=14, pady=(0, 14))

        self.page_titles = {
            "welcome": "Welcome",
            "list": "Mailing List",
            "compose": "Compose",
            "send": "Send & Schedule",
        }
        self.page_welcome = ttk.Frame(self.page_container, style="Panel.TFrame")
        self.tab_list = ttk.Frame(self.page_container, style="Panel.TFrame")
        self.tab_compose = ttk.Frame(self.page_container, style="Panel.TFrame")
        self.tab_send = ttk.Frame(self.page_container, style="Panel.TFrame")

        self.pages = {
            "welcome": self.page_welcome,
            "list": self.tab_list,
            "compose": self.tab_compose,
            "send": self.tab_send,
        }
        for frame in self.pages.values():
            frame.place(relx=0, rely=0, relwidth=1, relheight=1)

        self._build_welcome_page()
        self._build_list_tab()
        self._build_compose_tab()
        self._build_send_tab()

        self.show_page("welcome", animate=False)

    def _build_sidebar(self, parent):
        tk.Label(parent, text="Bulk Mailer", bg=SIDEBAR_BG, fg="#ffffff",
                 font=("Segoe UI", 14, "bold"), anchor="w", padx=18, pady=20).pack(fill="x")
        tk.Frame(parent, bg=SIDEBAR_BG_HOVER, height=1).pack(fill="x")

        self.nav_buttons = {}
        for key, label in [("welcome", "Welcome"), ("list", "Mailing List"),
                            ("compose", "Compose"), ("send", "Send & Schedule")]:
            btn = tk.Label(parent, text=label, bg=SIDEBAR_BG, fg=SIDEBAR_TEXT,
                            font=("Segoe UI", 10, "bold"), anchor="w",
                            padx=18, pady=13, cursor="hand2")
            btn.pack(fill="x")
            btn.bind("<Button-1>", lambda e, k=key: self.show_page(k))
            btn.bind("<Enter>", lambda e, b=btn, k=key: (
                b.configure(bg=SIDEBAR_BG_HOVER) if self.current_page != k else None))
            btn.bind("<Leave>", lambda e, b=btn, k=key: (
                b.configure(bg=SIDEBAR_ACTIVE_BG if self.current_page == k else SIDEBAR_BG)))
            self.nav_buttons[key] = btn

        tk.Frame(parent, bg=SIDEBAR_BG).pack(fill="both", expand=True)

        logout_btn = tk.Label(parent, text="Log Out", bg=SIDEBAR_BG, fg=SIDEBAR_TEXT_DIM,
                                font=("Segoe UI", 9, "bold"), anchor="w",
                                padx=18, pady=15, cursor="hand2")
        logout_btn.pack(fill="x", side="bottom")
        logout_btn.bind("<Button-1>", lambda e: self._logout())
        logout_btn.bind("<Enter>", lambda e: logout_btn.configure(fg="#ffffff"))
        logout_btn.bind("<Leave>", lambda e: logout_btn.configure(fg=SIDEBAR_TEXT_DIM))

    def show_page(self, name, animate=True):
        frame = self.pages.get(name)
        if frame is None:
            return
        frame.tkraise()
        self.current_page = name
        self.content_header_var.set(self.page_titles.get(name, ""))
        for key, btn in self.nav_buttons.items():
            active = key == name
            btn.configure(bg=SIDEBAR_ACTIVE_BG if active else SIDEBAR_BG,
                          fg="#ffffff" if active else SIDEBAR_TEXT)
        if name == "welcome":
            self._refresh_welcome_stats()
        if animate:
            self._animate_page_switch(frame)

    def _animate_page_switch(self, frame):
        """A brief, subtle accent-colored sweep under the page that was just
        switched to - kept thin and quick so it reads as a transition, not
        a flashy effect."""
        overlay = tk.Canvas(frame, height=2, highlightthickness=0, bd=0, bg=PANEL_BG)
        overlay.place(x=0, y=0, relwidth=1)
        bar = overlay.create_rectangle(0, 0, 50, 2, fill=ACCENT_CORAL, width=0)

        def step(x=0):
            if not overlay.winfo_exists():
                return
            width = overlay.winfo_width() or 400
            if x > width + 70:
                overlay.destroy()
                return
            overlay.coords(bar, x, 0, x + 50, 2)
            overlay.after(10, lambda: step(x + 45))

        frame.after(10, step)

    # ---------------- Welcome (landing) page ----------------

    def _build_welcome_page(self):
        frame = self.page_welcome

        hero = tk.Canvas(frame, height=130, highlightthickness=0, bd=0)
        hero.pack(fill="x")
        hero.bind("<Configure>", lambda e: self._draw_welcome_hero())
        self.welcome_hero_canvas = hero

        stats_row = ttk.Frame(frame, style="Panel.TFrame")
        stats_row.pack(fill="x", pady=16)
        self.stat_vars = {
            "total": tk.StringVar(value="0"),
            "sent": tk.StringVar(value="0"),
            "pending": tk.StringVar(value="0"),
        }
        for key, label in [("total", "Recipients"), ("sent", "Sent"), ("pending", "Pending")]:
            card = tk.Frame(stats_row, bg=PANEL_BG_2, padx=22, pady=16)
            card.pack(side="left", expand=True, fill="both", padx=(0, 12))
            tk.Label(card, textvariable=self.stat_vars[key], bg=PANEL_BG_2, fg=ACCENT_CORAL,
                     font=("Segoe UI", 24, "bold")).pack(anchor="w")
            tk.Label(card, text=label, bg=PANEL_BG_2, fg=TEXT_MUTED,
                     font=("Segoe UI", 9, "bold")).pack(anchor="w")

        actions = ttk.LabelFrame(frame, text="Quick actions")
        actions.pack(fill="x", pady=(0, 12))
        ttk.Button(actions, text="Manage Mailing List",
                   command=lambda: self.show_page("list")).pack(side="left", padx=10, pady=10)
        ttk.Button(actions, text="Compose an Email",
                   command=lambda: self.show_page("compose")).pack(side="left", padx=(0, 10))
        ttk.Button(actions, text="Send & Schedule",
                   command=lambda: self.show_page("send")).pack(side="left")

        ttk.Label(
            frame,
            text=("Tip: use Auto-Match Files / Auto-Match Folder on the Mailing List page to "
                  "attach a personal file per recipient automatically."),
            foreground=TEXT_MUTED, wraplength=680, justify="left"
        ).pack(fill="x", anchor="w")

    def _draw_welcome_hero(self):
        c = self.welcome_hero_canvas
        w = max(c.winfo_width(), 1)
        h = 130
        c.delete("all")
        bands = 44
        band_w = max(1, w // bands)
        for i in range(bands + 1):
            frac = i / bands
            color = sunset_color_at(frac, stops=HERO_STOPS)
            x0 = i * band_w
            c.create_rectangle(x0, 0, x0 + band_w + 1, h, fill=color, outline=color)
        c.create_text(26, h / 2 - 13, anchor="w", text="Welcome to Bulk Mailer",
                       font=("Segoe UI", 18, "bold"), fill="#ffffff")
        c.create_text(26, h / 2 + 16, anchor="w",
                       text="Manage your list, compose a message, and send personalized "
                            "campaigns in minutes.",
                       font=("Segoe UI", 10), fill="#dbe7ff")

    def _refresh_welcome_stats(self):
        total = len(self.mailing_list.records)
        sent = sum(1 for r in self.mailing_list.records if r["sent"])
        self.stat_vars["total"].set(str(total))
        self.stat_vars["sent"].set(str(sent))
        self.stat_vars["pending"].set(str(total - sent))

    # --- Mailing List tab ---

    def _build_list_tab(self):
        frame = self.tab_list

        # ── Row 1: Add email ──────────────────────────────────────────────
        top = ttk.Frame(frame)
        top.pack(fill="x", padx=8, pady=(8, 2))

        ttk.Label(top, text="Add (email or email|name):").pack(side="left")
        self.add_entry = ttk.Entry(top, width=36)
        self.add_entry.pack(side="left", padx=4)
        self.add_entry.bind("<Return>", lambda e: self._add_email())
        ttk.Button(top, text="Add", command=self._add_email).pack(side="left", padx=2)
        ttk.Button(top, text="Import CSV", command=self._import_csv).pack(side="left", padx=2)
        ttk.Button(top, text="Export CSV", command=self._export_csv).pack(side="left", padx=2)
        ttk.Button(top, text="Auto-Match Files...", command=self._auto_match_attachments).pack(side="left", padx=2)
        ttk.Button(top, text="Auto-Match Folder...", command=self._auto_match_folder).pack(side="left", padx=2)
        ttk.Button(top, text="Reset Sent Flags", command=self._reset_sent).pack(side="left", padx=8)

        # ── Row 2: Search / filter ────────────────────────────────────────
        search_frame = ttk.Frame(frame)
        search_frame.pack(fill="x", padx=8, pady=2)
        ttk.Label(search_frame, text="Search:").pack(side="left")
        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *a: self._apply_filter())
        self.search_entry = ttk.Entry(search_frame, textvariable=self.search_var, width=30)
        self.search_entry.pack(side="left", padx=4)
        ttk.Button(search_frame, text="Clear", command=self._clear_search).pack(side="left", padx=2)

        # ── Row 3: Multi-select controls ──────────────────────────────────
        sel_frame = ttk.LabelFrame(frame, text="Selection")
        sel_frame.pack(fill="x", padx=8, pady=4)

        ttk.Button(sel_frame, text="Select All",
                   command=self._select_all).pack(side="left", padx=4, pady=4)
        ttk.Button(sel_frame, text="Deselect All",
                   command=self._deselect_all).pack(side="left", padx=2)
        ttk.Button(sel_frame, text="Invert Selection",
                   command=self._invert_selection).pack(side="left", padx=2)
        ttk.Separator(sel_frame, orient="vertical").pack(side="left", fill="y", padx=6, pady=4)
        ttk.Button(sel_frame, text="Select Unsent",
                   command=self._select_unsent).pack(side="left", padx=2)
        ttk.Button(sel_frame, text="Select Sent",
                   command=self._select_sent).pack(side="left", padx=2)
        ttk.Separator(sel_frame, orient="vertical").pack(side="left", fill="y", padx=6, pady=4)
        ttk.Button(sel_frame, text="Remove Selected",
                   command=self._remove_selected).pack(side="left", padx=2)
        ttk.Button(sel_frame, text="Export Selected",
                   command=self._export_selected).pack(side="left", padx=2)
        ttk.Separator(sel_frame, orient="vertical").pack(side="left", fill="y", padx=6, pady=4)
        ttk.Button(sel_frame, text="Set Attachment for Selected",
                   command=self._set_attachment_selected).pack(side="left", padx=2)
        ttk.Button(sel_frame, text="Clear Attachment for Selected",
                   command=self._clear_attachment_selected).pack(side="left", padx=2)

        # selection counter label
        self.sel_count_var = tk.StringVar(value="0 selected")
        ttk.Label(sel_frame, textvariable=self.sel_count_var,
                  foreground="gray").pack(side="right", padx=8)

        # ── Row 4: Sort ───────────────────────────────────────────────────
        sort_frame = ttk.Frame(frame)
        sort_frame.pack(fill="x", padx=8, pady=2)
        ttk.Label(sort_frame, text="Sort by:").pack(side="left")
        for label, key in [("Email", "email"), ("Name", "name"),
                            ("Domain", "domain"), ("Date Added", "date"),
                            ("Sent", "sent")]:
            ttk.Button(sort_frame, text=label, width=10,
                       command=lambda k=key: self._sort(k)).pack(side="left", padx=2)

        # ── Treeview ──────────────────────────────────────────────────────
        tree_frame = ttk.Frame(frame)
        tree_frame.pack(fill="both", expand=True, padx=8, pady=4)

        columns = ("name", "email", "attachment_path", "date_added", "sent", "last_sent")
        self.tree = ttk.Treeview(tree_frame, columns=columns, show="headings",
                                  selectmode="extended")
        for col, lbl, w in [("name", "Name", 150), ("email", "Email", 220),
                              ("attachment_path", "Attachment File", 200),
                              ("date_added", "Date Added", 140),
                              ("sent", "Sent", 55), ("last_sent", "Last Sent", 140)]:
            self.tree.heading(col, text=lbl,
                              command=lambda c=col: self._sort_by_column(c))
            self.tree.column(col, width=w, anchor="w")

        # tag colours for sent/unsent rows
        self.tree.tag_configure("sent_row",   background=SENT_ROW_BG, foreground=TEXT_MUTED)
        self.tree.tag_configure("unsent_row", background=ROW_BG, foreground=TEXT_LIGHT)

        vsb = ttk.Scrollbar(tree_frame, orient="vertical", command=self.tree.yview)
        hsb = ttk.Scrollbar(tree_frame, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)

        self.tree.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")
        hsb.grid(row=1, column=0, sticky="ew")
        tree_frame.rowconfigure(0, weight=1)
        tree_frame.columnconfigure(0, weight=1)

        # bind selection change to update counter
        self.tree.bind("<<TreeviewSelect>>", self._on_tree_select)

        # right-click context menu
        self._build_context_menu()
        self.tree.bind("<Button-3>", self._show_context_menu)   # Windows/Linux
        self.tree.bind("<Button-2>", self._show_context_menu)   # macOS

        self._refresh_tree()

    def _build_context_menu(self):
        self.context_menu = tk.Menu(self.root, tearoff=0, bg=PANEL_BG_2, fg=TEXT_LIGHT,
                                     activebackground=ACCENT_CORAL, activeforeground="#ffffff",
                                     bd=0)
        self.context_menu.add_command(label="Select All",        command=self._select_all)
        self.context_menu.add_command(label="Deselect All",      command=self._deselect_all)
        self.context_menu.add_command(label="Invert Selection",  command=self._invert_selection)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="Select Unsent",     command=self._select_unsent)
        self.context_menu.add_command(label="Select Sent",       command=self._select_sent)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="Remove Selected",   command=self._remove_selected)
        self.context_menu.add_command(label="Export Selected",   command=self._export_selected)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="Set Attachment for Selected",
                                       command=self._set_attachment_selected)
        self.context_menu.add_command(label="Clear Attachment for Selected",
                                       command=self._clear_attachment_selected)
        self.context_menu.add_command(label="Auto-Match Files...",
                                       command=self._auto_match_attachments)
        self.context_menu.add_command(label="Auto-Match Folder...",
                                       command=self._auto_match_folder)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="Reset Sent Flags for Selected",
                                       command=self._reset_sent_selected)

    def _show_context_menu(self, event):
        # select the row under the cursor if not already selected
        item = self.tree.identify_row(event.y)
        if item and item not in self.tree.selection():
            self.tree.selection_set(item)
        try:
            self.context_menu.tk_popup(event.x_root, event.y_root)
        finally:
            self.context_menu.grab_release()

    # ── Selection helpers ─────────────────────────────────────────────────

    def _on_tree_select(self, event=None):
        n = len(self.tree.selection())
        total = len(self.tree.get_children())
        self.sel_count_var.set(f"{n} of {total} selected")

    def _select_all(self):
        self.tree.selection_set(self.tree.get_children())
        self._on_tree_select()

    def _deselect_all(self):
        self.tree.selection_remove(self.tree.get_children())
        self._on_tree_select()

    def _invert_selection(self):
        all_items = set(self.tree.get_children())
        current = set(self.tree.selection())
        self.tree.selection_set(list(all_items - current))
        self._on_tree_select()

    def _select_unsent(self):
        self.tree.selection_remove(self.tree.get_children())
        for item in self.tree.get_children():
            if self.tree.item(item, "values")[4] == "No":
                self.tree.selection_add(item)
        self._on_tree_select()

    def _select_sent(self):
        self.tree.selection_remove(self.tree.get_children())
        for item in self.tree.get_children():
            if self.tree.item(item, "values")[4] == "Yes":
                self.tree.selection_add(item)
        self._on_tree_select()

    # ── Search / filter ───────────────────────────────────────────────────

    def _apply_filter(self):
        query = self.search_var.get().lower().strip()
        self.tree.delete(*self.tree.get_children())
        for r in self.mailing_list.records:
            if (query in r["email"].lower() or
                    query in r["name"].lower()):
                tag = "sent_row" if r["sent"] else "unsent_row"
                self.tree.insert("", "end", values=(
                    r["name"], r["email"], r.get("attachment_path", ""),
                    r["date_added"], "Yes" if r["sent"] else "No",
                    r["last_sent"] or ""), tags=(tag,))
        self._on_tree_select()

    def _clear_search(self):
        self.search_var.set("")
        self._refresh_tree()

    # ── Column header sort ────────────────────────────────────────────────

    def _sort_by_column(self, col):
        key_map = {
            "email": "email", "name": "name",
            "date_added": "date", "sent": "sent", "last_sent": "date"
        }
        self._sort(key_map.get(col, col))

    # ── Export selected only ──────────────────────────────────────────────

    def _export_selected(self):
        sel = self.tree.selection()
        if not sel:
            messagebox.showinfo("Export Selected", "No rows selected.")
            return
        emails = {self.tree.item(i, "values")[1] for i in sel}
        records = [r for r in self.mailing_list.records if r["email"] in emails]
        path = filedialog.asksaveasfilename(defaultextension=".csv",
                                             filetypes=[("CSV files", "*.csv")])
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8", newline="") as f:
                import csv as _csv
                w = _csv.writer(f)
                w.writerow(["name", "email", "attachment_path", "date_added", "sent", "last_sent"])
                for r in records:
                    w.writerow([r["name"], r["email"], r.get("attachment_path", ""),
                                 r["date_added"], r["sent"], r["last_sent"] or ""])
            messagebox.showinfo("Export Selected",
                                 f"Exported {len(records)} selected recipients to {path}")
        except Exception as e:
            messagebox.showerror("Export Selected", str(e))

    # ── Set / clear per-recipient attachment ──────────────────────────────

    def _set_attachment_selected(self):
        sel = self.tree.selection()
        if not sel:
            messagebox.showinfo("Set Attachment", "No rows selected.")
            return
        path = filedialog.askopenfilename(title="Choose file to attach for selected recipients")
        if not path:
            return
        emails = [self.tree.item(i, "values")[1] for i in sel]
        for email in emails:
            self.mailing_list.set_attachment(email, path)
        self._refresh_tree()
        logger.info(f"Set attachment '{os.path.basename(path)}' for {len(emails)} recipient(s)")

    def _clear_attachment_selected(self):
        sel = self.tree.selection()
        if not sel:
            messagebox.showinfo("Clear Attachment", "No rows selected.")
            return
        emails = [self.tree.item(i, "values")[1] for i in sel]
        for email in emails:
            self.mailing_list.set_attachment(email, "")
        self._refresh_tree()
        logger.info(f"Cleared attachment for {len(emails)} recipient(s)")

    # ── Auto-match a batch of files to recipients by filename ─────────────

    @staticmethod
    def _norm(s):
        return re.sub(r"[^a-z0-9]", "", (s or "").lower())

    def _match_files_to_recipients(self, paths):
        """
        For each file path, find recipients whose name or email appears in
        the filename (exact substring match), falling back to a fuzzy
        similarity match when nothing matches directly.
        Returns a list of dicts: {path, filename, exact: [emails], fuzzy: [emails]}
        """
        records = self.mailing_list.records
        results = []
        for path in paths:
            fname = os.path.basename(path)
            base = os.path.splitext(fname)[0]
            fname_norm = self._norm(base)
            exact = []
            fuzzy_scored = []
            for r in records:
                email_local_norm = self._norm(r["email"].split("@")[0])
                email_full_norm = self._norm(r["email"])
                name_norm = self._norm(r.get("name", ""))
                is_exact = (
                    (email_local_norm and email_local_norm in fname_norm) or
                    (email_full_norm and email_full_norm in fname_norm) or
                    (name_norm and len(name_norm) >= 3 and name_norm in fname_norm)
                )
                if is_exact:
                    exact.append(r["email"])
                    continue
                best_ratio = 0.0
                for candidate in (name_norm, email_local_norm):
                    if not candidate:
                        continue
                    ratio = difflib.SequenceMatcher(None, candidate, fname_norm).ratio()
                    best_ratio = max(best_ratio, ratio)
                if best_ratio >= 0.6:
                    fuzzy_scored.append((r["email"], best_ratio))
            fuzzy_scored.sort(key=lambda x: -x[1])
            results.append({
                "path": path,
                "filename": fname,
                "exact": exact,
                "fuzzy": [e for e, _ in fuzzy_scored],
            })
        return results

    def _auto_match_attachments(self):
        """Pick a batch of files and auto-assign each one to the recipient
        whose name/email best matches the filename, with a review step
        before anything is applied."""
        if not self.mailing_list.records:
            messagebox.showinfo("Auto-Match", "Add recipients to the mailing list first.")
            return
        paths = filedialog.askopenfilenames(
            title="Select files to auto-match to recipients (by filename)")
        if not paths:
            return
        self._run_auto_match_dialog(paths)

    def _auto_match_folder(self):
        """Load every file in a chosen folder at once and auto-assign each
        one to the recipient whose name/email best matches the filename."""
        if not self.mailing_list.records:
            messagebox.showinfo("Auto-Match", "Add recipients to the mailing list first.")
            return
        folder = filedialog.askdirectory(title="Select a folder of files to auto-match")
        if not folder:
            return
        paths = sorted(
            os.path.join(folder, fname)
            for fname in os.listdir(folder)
            if os.path.isfile(os.path.join(folder, fname))
        )
        if not paths:
            messagebox.showinfo("Auto-Match", "That folder doesn't contain any files.")
            return
        self._run_auto_match_dialog(paths)

    def _run_auto_match_dialog(self, paths):
        """Shared entry point used by both the file-picker and folder-picker.
        A single file with one confident match gets a quick yes/no confirm
        instead of the full review table; anything else (multiple files, or
        an ambiguous/fuzzy/no match) falls through to the full table below so
        you can pick manually."""
        matches = self._match_files_to_recipients(paths)

        if len(matches) == 1 and len(matches[0]["exact"]) == 1:
            self._quick_confirm_single_match(matches[0])
            return

        self._show_auto_match_table(matches)

    def _quick_confirm_single_match(self, match):
        """Fast path for adding one file at a time: ask a single yes/no
        question instead of opening the full table."""
        email = match["exact"][0]
        record = next((r for r in self.mailing_list.records if r["email"] == email), None)
        display = f"{record['name']} <{email}>" if record and record.get("name") else email
        proceed = messagebox.askyesno(
            "Attach File",
            f"Attach '{match['filename']}' to {display}?\n\n"
            "Choose No to pick a different recipient instead."
        )
        if proceed:
            self.mailing_list.set_attachment(email, match["path"])
            self._refresh_tree()
            logger.info(f"Auto-match: attached '{match['filename']}' to {email}")
        else:
            # Let them pick manually via the full table instead of forcing the guess.
            self._show_auto_match_table([match])

    def _show_auto_match_table(self, matches):
        """The full multi-row review table, used for bulk adds and for any
        single file that didn't have one clear, confident match."""
        paths = [m["path"] for m in matches]

        win = tk.Toplevel(self.root)
        win.title("Auto-Match Files to Recipients")
        win.geometry("780x540")
        win.configure(bg=PANEL_BG)
        win.transient(self.root)

        ttk.Label(
            win,
            text=(f"{len(paths)} file(s) selected. Files are matched to recipients by "
                  "looking for their name or email inside the filename. Review or change "
                  "any row below, then click Apply."),
            wraplength=740, justify="left"
        ).pack(anchor="w", padx=10, pady=(10, 4))

        # Build recipient display list for the dropdowns
        disp_to_email = {}
        email_to_disp = {}
        disp_list = []
        for r in self.mailing_list.records:
            disp = f"{r['name']} <{r['email']}>" if r.get("name") else r["email"]
            disp_to_email[disp] = r["email"]
            email_to_disp[r["email"]] = disp
            disp_list.append(disp)
        disp_list.sort(key=str.lower)
        SKIP = "-- Skip this file --"
        combo_values = [SKIP] + disp_list

        # Scrollable rows area
        container = ttk.Frame(win)
        container.pack(fill="both", expand=True, padx=10, pady=4)
        canvas = tk.Canvas(container, highlightthickness=0, bg=PANEL_BG)
        vsb = ttk.Scrollbar(container, orient="vertical", command=canvas.yview)
        inner = ttk.Frame(canvas)
        inner.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=inner, anchor="nw")
        canvas.configure(yscrollcommand=vsb.set)
        canvas.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")

        def _wheel(event):
            delta = event.delta if event.delta else (120 if event.num == 4 else -120)
            canvas.yview_scroll(int(-1 * (delta / 120)), "units")
        canvas.bind_all("<MouseWheel>", _wheel)
        canvas.bind_all("<Button-4>", _wheel)
        canvas.bind_all("<Button-5>", _wheel)

        def _cleanup_bindings():
            canvas.unbind_all("<MouseWheel>")
            canvas.unbind_all("<Button-4>")
            canvas.unbind_all("<Button-5>")
            win.destroy()
        win.protocol("WM_DELETE_WINDOW", _cleanup_bindings)

        ttk.Label(inner, text="File", font=("TkDefaultFont", 9, "bold")).grid(
            row=0, column=0, sticky="w", padx=4, pady=4)
        ttk.Label(inner, text="Match status", font=("TkDefaultFont", 9, "bold")).grid(
            row=0, column=1, sticky="w", padx=4)
        ttk.Label(inner, text="Assign to recipient", font=("TkDefaultFont", 9, "bold")).grid(
            row=0, column=2, sticky="w", padx=4)

        row_vars = []
        auto_matched_count = 0
        for i, m in enumerate(matches, start=1):
            ttk.Label(inner, text=m["filename"]).grid(row=i, column=0, sticky="w", padx=4, pady=2)

            var = tk.StringVar()
            if len(m["exact"]) == 1:
                var.set(email_to_disp.get(m["exact"][0], SKIP))
                status, fg = "Matched", "#2a7a2a"
                auto_matched_count += 1
            elif len(m["exact"]) > 1:
                var.set(SKIP)
                status, fg = f"Ambiguous ({len(m['exact'])} candidates) - pick one", "#c07800"
            elif m["fuzzy"]:
                var.set(email_to_disp.get(m["fuzzy"][0], SKIP))
                status, fg = "Fuzzy match - please confirm", "#c07800"
            else:
                var.set(SKIP)
                status, fg = "No match found", "#999999"

            ttk.Label(inner, text=status, foreground=fg).grid(row=i, column=1, sticky="w", padx=4)
            combo = ttk.Combobox(inner, textvariable=var, values=combo_values,
                                  width=42, state="readonly")
            combo.grid(row=i, column=2, sticky="w", padx=4, pady=2)
            row_vars.append((m["path"], var))

        summary_var = tk.StringVar(
            value=f"{auto_matched_count} of {len(matches)} file(s) auto-matched with high "
                  "confidence. Review ambiguous / fuzzy / unmatched rows before applying.")
        ttk.Label(win, textvariable=summary_var, foreground="gray",
                  wraplength=740, justify="left").pack(anchor="w", padx=10, pady=(4, 4))

        btn_row = ttk.Frame(win)
        btn_row.pack(fill="x", padx=10, pady=10)

        def apply():
            applied = 0
            for path, var in row_vars:
                disp = var.get()
                if disp == SKIP or disp not in disp_to_email:
                    continue
                email = disp_to_email[disp]
                self.mailing_list.set_attachment(email, path)
                applied += 1
            self._refresh_tree()
            logger.info(
                f"Auto-match: applied attachments to {applied} recipient(s) "
                f"from {len(matches)} file(s)")
            messagebox.showinfo("Auto-Match", f"Applied {applied} attachment(s).")
            _cleanup_bindings()

        ttk.Button(btn_row, text="Apply", command=apply).pack(side="left", padx=4)
        ttk.Button(btn_row, text="Cancel", command=_cleanup_bindings).pack(side="left", padx=4)

    # ── Reset sent flags for selected only ────────────────────────────────

    def _reset_sent_selected(self):
        sel = self.tree.selection()
        if not sel:
            return
        emails = [self.tree.item(i, "values")[1] for i in sel]
        if messagebox.askyesno("Confirm",
                                f"Reset sent flag for {len(emails)} selected recipient(s)?"):
            self.mailing_list.reset_sent_flags(emails)
            self._refresh_tree()

    def _refresh_tree(self):
        self.tree.delete(*self.tree.get_children())
        query = self.search_var.get().lower().strip() if hasattr(self, "search_var") else ""
        for r in self.mailing_list.records:
            if query and query not in r["email"].lower() and query not in r["name"].lower():
                continue
            tag = "sent_row" if r["sent"] else "unsent_row"
            self.tree.insert("", "end", values=(
                r["name"], r["email"], r.get("attachment_path", ""),
                r["date_added"], "Yes" if r["sent"] else "No",
                r["last_sent"] or ""), tags=(tag,))
        total = len(self.mailing_list.records)
        shown = len(self.tree.get_children())
        self.status_var.set(
            f"{total} recipients in list" +
            (f"  |  {shown} shown (filter active)" if query else ""))
        if hasattr(self, "sel_count_var"):
            self._on_tree_select()

    def _add_email(self):
        line = self.add_entry.get()
        ok, msg = self.mailing_list.add_raw_line(line)
        if ok:
            self.add_entry.delete(0, "end")
            self._refresh_tree()
            logger.info(f"Added recipient: {line}")
        else:
            messagebox.showwarning("Add Email", msg)

    def _remove_selected(self):
        sel = self.tree.selection()
        if not sel:
            return
        emails = [self.tree.item(i, "values")[1] for i in sel]
        if not messagebox.askyesno("Confirm", f"Remove {len(emails)} recipient(s)?"):
            return
        n = self.mailing_list.remove(emails)
        self._refresh_tree()
        logger.info(f"Removed {n} recipient(s)")

    def _import_csv(self):
        path = filedialog.askopenfilename(filetypes=[("CSV files", "*.csv")])
        if not path:
            return
        try:
            added, skipped = self.mailing_list.import_csv(path)
            self._refresh_tree()
            messagebox.showinfo("Import CSV", f"Added: {added}\nSkipped: {skipped}")
            logger.info(f"Imported CSV {path}: added={added}, skipped={skipped}")
        except Exception as e:
            messagebox.showerror("Import CSV", str(e))
            logger.error(f"CSV import failed: {e}")

    def _export_csv(self):
        path = filedialog.asksaveasfilename(defaultextension=".csv",
                                             filetypes=[("CSV files", "*.csv")])
        if not path:
            return
        try:
            self.mailing_list.export_csv(path)
            messagebox.showinfo("Export CSV", f"Exported to {path}")
            logger.info(f"Exported mailing list to {path}")
        except Exception as e:
            messagebox.showerror("Export CSV", str(e))

    def _reset_sent(self):
        if messagebox.askyesno("Confirm", "Reset 'sent' flag for ALL recipients?"):
            self.mailing_list.reset_sent_flags()
            self._refresh_tree()

    def _sort(self, key):
        self.mailing_list.sort_by(key)
        self._refresh_tree()

    # --- Compose tab ---

    def _build_compose_tab(self):
        frame = self.tab_compose
        top = ttk.Frame(frame)
        top.pack(fill="x", padx=8, pady=6)

        ttk.Label(top, text="Subject:").pack(side="left")
        self.subject_entry = ttk.Entry(top, width=60)
        self.subject_entry.pack(side="left", padx=4)

        self.mode_var = tk.StringVar(value="plain")
        ttk.Radiobutton(top, text="Plain Text", variable=self.mode_var,
                        value="plain").pack(side="left", padx=10)
        ttk.Radiobutton(top, text="HTML", variable=self.mode_var,
                        value="html").pack(side="left")

        fmt_bar = ttk.Frame(frame)
        fmt_bar.pack(fill="x", padx=8)
        ttk.Label(fmt_bar, text="HTML helpers:").pack(side="left")
        for label, tag in [("Bold", ("<b>", "</b>")), ("Italic", ("<i>", "</i>")),
                            ("Link", ("<a href='URL'>", "</a>")),
                            ("Para", ("<p>", "</p>")), ("Line break", ("<br>", ""))]:
            ttk.Button(fmt_bar, text=label, width=8,
                       command=lambda t=tag: self._insert_tag(t)).pack(side="left", padx=2)
        ttk.Label(fmt_bar, text="  Use {{name}} as a personalization placeholder").pack(side="left", padx=10)

        self.body_text = tk.Text(frame, wrap="word", undo=True, bg=INPUT_BG, fg=TEXT_LIGHT,
                                   insertbackground=TEXT_LIGHT, selectbackground=ACCENT_CORAL,
                                   selectforeground="#ffffff", relief="flat", bd=6,
                                   highlightthickness=1, highlightbackground=ACCENT_DEEP,
                                   highlightcolor=ACCENT_GOLD)
        self.body_text.pack(fill="both", expand=True, padx=8, pady=6)

        attach_frame = ttk.LabelFrame(frame, text="Attachments (sent to every recipient)")
        attach_frame.pack(fill="x", padx=8, pady=6)
        btn_row = ttk.Frame(attach_frame)
        btn_row.pack(fill="x")
        ttk.Button(btn_row, text="Add Files", command=self._add_attachments).pack(side="left", padx=2, pady=4)
        ttk.Button(btn_row, text="Remove Selected", command=self._remove_attachments).pack(side="left", padx=2)
        self.attach_listbox = tk.Listbox(attach_frame, height=4, selectmode="extended",
                                          bg=INPUT_BG, fg=TEXT_LIGHT,
                                          selectbackground=ACCENT_CORAL,
                                          selectforeground="#ffffff", relief="flat", bd=4,
                                          highlightthickness=1, highlightbackground=ACCENT_DEEP)
        self.attach_listbox.pack(fill="x", padx=4, pady=4)
        ttk.Label(attach_frame,
                  text="Tip: to send a different file per person, use 'Set Attachment for "
                       "Selected' on the Mailing List tab instead.",
                  foreground="gray").pack(anchor="w", padx=4, pady=(0, 4))

    def _insert_tag(self, tag_pair):
        open_tag, close_tag = tag_pair
        try:
            sel = self.body_text.get("sel.first", "sel.last")
        except tk.TclError:
            sel = ""
        self.body_text.insert("insert", f"{open_tag}{sel}{close_tag}")

    def _add_attachments(self):
        paths = filedialog.askopenfilenames()
        for p in paths:
            if p not in self.attachments:
                self.attachments.append(p)
                self.attach_listbox.insert("end", os.path.basename(p))

    def _remove_attachments(self):
        sel = list(self.attach_listbox.curselection())
        for idx in reversed(sel):
            self.attach_listbox.delete(idx)
            del self.attachments[idx]

    # --- Send & Schedule tab ---

    def _build_send_tab(self):
        frame = self.tab_send

        provider_frame = ttk.LabelFrame(frame, text="Provider / SMTP Settings")
        provider_frame.pack(fill="x", padx=8, pady=6)

        ttk.Label(provider_frame, text="Provider:").grid(row=0, column=0, sticky="w", padx=4, pady=3)
        self.provider_var = tk.StringVar(value="Gmail")
        provider_combo = ttk.Combobox(provider_frame, textvariable=self.provider_var,
                                       values=list(PROVIDERS.keys()), state="readonly", width=20)
        provider_combo.grid(row=0, column=1, sticky="w", padx=4)
        provider_combo.bind("<<ComboboxSelected>>", self._on_provider_change)

        ttk.Label(provider_frame, text="Server:").grid(row=1, column=0, sticky="w", padx=4)
        self.server_entry = ttk.Entry(provider_frame, width=30)
        self.server_entry.grid(row=1, column=1, sticky="w", padx=4)

        ttk.Label(provider_frame, text="Port:").grid(row=1, column=2, sticky="w", padx=4)
        self.port_entry = ttk.Entry(provider_frame, width=8)
        self.port_entry.grid(row=1, column=3, sticky="w", padx=4)

        self.tls_var = tk.BooleanVar(value=True)
        self.ssl_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(provider_frame, text="STARTTLS", variable=self.tls_var).grid(row=1, column=4, padx=4)
        ttk.Checkbutton(provider_frame, text="SSL", variable=self.ssl_var).grid(row=1, column=5, padx=4)

        ttk.Label(provider_frame, text="Username:").grid(row=2, column=0, sticky="w", padx=4)
        self.username_entry = ttk.Entry(provider_frame, width=30)
        self.username_entry.grid(row=2, column=1, sticky="w", padx=4)

        ttk.Label(provider_frame, text="Password / App Password:").grid(row=2, column=2, sticky="w", padx=4)
        self.password_entry = ttk.Entry(provider_frame, width=24, show="*")
        self.password_entry.grid(row=2, column=3, sticky="w", padx=4, columnspan=2)

        ttk.Button(provider_frame, text="Load from ENV (SMTP_USER/SMTP_PASS)",
                   command=self._load_env_creds).grid(row=2, column=5, padx=4)

        self._on_provider_change()

        recip_frame = ttk.LabelFrame(frame, text="Recipients")
        recip_frame.pack(fill="x", padx=8, pady=6)
        self.recipient_mode = tk.StringVar(value="all_unsent")
        ttk.Radiobutton(recip_frame, text="All (unsent only)", variable=self.recipient_mode,
                        value="all_unsent").pack(side="left", padx=4)
        ttk.Radiobutton(recip_frame, text="All (incl. already sent)", variable=self.recipient_mode,
                        value="all").pack(side="left", padx=4)
        ttk.Radiobutton(recip_frame, text="Selected in Mailing List tab", variable=self.recipient_mode,
                        value="selected").pack(side="left", padx=4)
        ttk.Radiobutton(recip_frame, text="Only recipients with an attached file", variable=self.recipient_mode,
                        value="with_attachment").pack(side="left", padx=4)

        batch_frame = ttk.LabelFrame(frame, text="Batching & Rate Limiting")
        batch_frame.pack(fill="x", padx=8, pady=6)
        ttk.Label(batch_frame, text="Batch size:").pack(side="left", padx=4)
        self.batch_size_entry = ttk.Entry(batch_frame, width=6)
        self.batch_size_entry.insert(0, "20")
        self.batch_size_entry.pack(side="left")
        ttk.Label(batch_frame, text="Delay between batches (sec):").pack(side="left", padx=4)
        self.delay_entry = ttk.Entry(batch_frame, width=6)
        self.delay_entry.insert(0, "5")
        self.delay_entry.pack(side="left")

        sched_frame = ttk.LabelFrame(frame, text="Scheduling (optional)")
        sched_frame.pack(fill="x", padx=8, pady=6)
        self.schedule_enabled = tk.BooleanVar(value=False)
        ttk.Checkbutton(sched_frame, text="Schedule for later", variable=self.schedule_enabled).pack(side="left", padx=4)
        ttk.Label(sched_frame, text="Date (YYYY-MM-DD):").pack(side="left", padx=4)
        self.sched_date_entry = ttk.Entry(sched_frame, width=12)
        self.sched_date_entry.insert(0, datetime.now().strftime("%Y-%m-%d"))
        self.sched_date_entry.pack(side="left")
        ttk.Label(sched_frame, text="Time (HH:MM, 24h, local):").pack(side="left", padx=4)
        self.sched_time_entry = ttk.Entry(sched_frame, width=8)
        self.sched_time_entry.insert(0, "09:00")
        self.sched_time_entry.pack(side="left")

        action_frame = ttk.Frame(frame)
        action_frame.pack(fill="x", padx=8, pady=10)
        ttk.Button(action_frame, text="Preview", command=self._preview).pack(side="left", padx=4)
        ttk.Button(action_frame, text="Dry Run", command=lambda: self._start_send(dry_run=True)).pack(side="left", padx=4)
        ttk.Button(action_frame, text="Send Now", command=lambda: self._start_send(dry_run=False)).pack(side="left", padx=4)
        ttk.Button(action_frame, text="Schedule / Queue", command=self._schedule_send).pack(side="left", padx=4)
        ttk.Button(action_frame, text="Cancel Sending", command=self._cancel_send).pack(side="left", padx=12)

        self.progress = ttk.Progressbar(frame, mode="determinate")
        self.progress.pack(fill="x", padx=8, pady=4)

        log_frame = ttk.LabelFrame(frame, text="Log")
        log_frame.pack(fill="both", expand=True, padx=8, pady=6)
        self.log_text = tk.Text(log_frame, height=10, state="disabled", wrap="word",
                                  bg=INPUT_BG, fg=TEXT_LIGHT, insertbackground=TEXT_LIGHT,
                                  selectbackground=ACCENT_CORAL, selectforeground="#ffffff",
                                  relief="flat", bd=6, highlightthickness=1,
                                  highlightbackground=ACCENT_DEEP)
        self.log_text.pack(fill="both", expand=True, padx=4, pady=4)
        logger.addHandler(GuiLogHandler(self.log_text))

    def _on_provider_change(self, event=None):
        p = PROVIDERS[self.provider_var.get()]
        self.server_entry.delete(0, "end"); self.server_entry.insert(0, p["server"])
        self.port_entry.delete(0, "end"); self.port_entry.insert(0, str(p["port"]))
        self.tls_var.set(p["tls"])
        self.ssl_var.set(p["ssl"])

    def _load_env_creds(self):
        user = os.environ.get("SMTP_USER", "")
        pw = os.environ.get("SMTP_PASS", "")
        if not user or not pw:
            messagebox.showwarning("ENV Credentials",
                                    "Set SMTP_USER and SMTP_PASS environment variables first.")
            return
        self.username_entry.delete(0, "end"); self.username_entry.insert(0, user)
        self.password_entry.delete(0, "end"); self.password_entry.insert(0, pw)
        logger.info("Loaded credentials from environment variables.")

    # --- gathering state ---

    def _get_credentials(self):
        return SmtpCredentials(
            server=self.server_entry.get().strip(),
            port=self.port_entry.get().strip() or 587,
            use_tls=self.tls_var.get(),
            use_ssl=self.ssl_var.get(),
            username=self.username_entry.get().strip(),
            password=self.password_entry.get(),
        )

    def _get_recipients(self):
        mode = self.recipient_mode.get()
        if mode == "selected":
            sel = self.tree.selection()
            emails = {self.tree.item(i, "values")[1] for i in sel}
            return [r for r in self.mailing_list.records if r["email"] in emails]
        elif mode == "all":
            return list(self.mailing_list.records)
        elif mode == "with_attachment":
            return [r for r in self.mailing_list.records
                    if r.get("attachment_path", "").strip()
                    and os.path.isfile(r["attachment_path"])]
        else:  # all_unsent
            return [r for r in self.mailing_list.records if not r["sent"]]

    def _validate_compose(self):
        subject = self.subject_entry.get().strip()
        body = self.body_text.get("1.0", "end-1c")
        if not subject:
            raise ValueError("Subject is empty.")
        if not body.strip():
            raise ValueError("Body is empty.")
        return subject, body

    def _preview(self):
        try:
            subject, body = self._validate_compose()
        except ValueError as e:
            messagebox.showwarning("Preview", str(e))
            return
        recipients = self._get_recipients()
        win = tk.Toplevel(self.root)
        win.title("Preview")
        win.geometry("500x500")
        win.configure(bg=PANEL_BG)
        ttk.Label(win, text=f"Subject: {subject}", font=("TkDefaultFont", 10, "bold")).pack(anchor="w", padx=8, pady=4)
        ttk.Label(win, text=f"Recipients: {len(recipients)}  |  Mode: {self.mode_var.get()}").pack(anchor="w", padx=8)
        per_recipient_files = sum(1 for r in recipients if r.get("attachment_path", "").strip())
        if per_recipient_files:
            ttk.Label(win, text=f"{per_recipient_files} recipient(s) have a personal attachment set").pack(
                anchor="w", padx=8)
        txt = tk.Text(win, wrap="word", bg=INPUT_BG, fg=TEXT_LIGHT, insertbackground=TEXT_LIGHT,
                       relief="flat", bd=6, highlightthickness=1, highlightbackground=ACCENT_DEEP)
        sample_name = recipients[0]["name"] if recipients else "Friend"
        txt.insert("1.0", body.replace("{{name}}", sample_name or "Friend"))
        txt.configure(state="disabled")
        txt.pack(fill="both", expand=True, padx=8, pady=8)

    # --- sending ---

    def _start_send(self, dry_run):
        try:
            subject, body = self._validate_compose()
        except ValueError as e:
            messagebox.showwarning("Compose", str(e))
            return

        recipients = self._get_recipients()
        if not recipients:
            messagebox.showinfo("Send", "No recipients match the current selection mode.")
            return

        creds = self._get_credentials()
        if not dry_run and (not creds.server or not creds.username or not creds.password):
            messagebox.showwarning("Credentials", "Server, username and password are required to send.")
            return

        try:
            batch_size = max(1, int(self.batch_size_entry.get()))
            delay = max(0, float(self.delay_entry.get()))
        except ValueError:
            messagebox.showwarning("Settings", "Batch size and delay must be numbers.")
            return

        if self.send_thread and self.send_thread.is_alive():
            messagebox.showinfo("Send", "A send operation is already in progress.")
            return

        self.cancel_requested = False
        self.progress["value"] = 0
        self.progress["maximum"] = len(recipients)
        is_html = self.mode_var.get() == "html"
        attachments = list(self.attachments)

        def worker():
            sender = EmailSender(creds)

            def progress_cb(done, total, addr, ok):
                self.root.after(0, lambda: self._update_progress(done, total))

            try:
                sent, failed = sender.send_batches(
                    recipients, subject, body, is_html, attachments,
                    batch_size, delay, self.mailing_list,
                    progress_cb=progress_cb,
                    stop_flag=lambda: self.cancel_requested,
                    dry_run=dry_run,
                )
                self.root.after(0, lambda: self._refresh_tree())
                self.root.after(0, lambda: messagebox.showinfo(
                    "Send Complete",
                    f"{'Dry run' if dry_run else 'Send'} finished.\n"
                    f"Processed: {sent}\nFailed: {len(failed)}"
                    + (f"\n\nFailed addresses:\n{chr(10).join(failed)}" if failed else "")
                ))
            except smtplib.SMTPAuthenticationError as e:
                self.root.after(0, lambda: messagebox.showerror(
                    "Authentication Failed",
                    "SMTP login failed. Check username/password (or use an app password).\n"
                    f"Details: {e}"))
            except (smtplib.SMTPConnectError, OSError) as e:
                self.root.after(0, lambda: messagebox.showerror(
                    "Connection Failed", f"Could not connect to SMTP server.\nDetails: {e}"))
            except Exception as e:
                logger.error(f"Unexpected error during send: {e}")
                self.root.after(0, lambda: messagebox.showerror("Error", str(e)))

        self.send_thread = threading.Thread(target=worker, daemon=True)
        self.send_thread.start()

    def _update_progress(self, done, total):
        self.progress["value"] = done
        self.status_var.set(f"Sending... {done}/{total}")

    def _cancel_send(self):
        self.cancel_requested = True
        self.status_var.set("Cancel requested...")

    # --- scheduling ---

    def _schedule_send(self):
        try:
            subject, body = self._validate_compose()
        except ValueError as e:
            messagebox.showwarning("Compose", str(e))
            return
        recipients = self._get_recipients()
        if not recipients:
            messagebox.showinfo("Schedule", "No recipients match the current selection mode.")
            return
        creds = self._get_credentials()
        if not creds.server or not creds.username or not creds.password:
            messagebox.showwarning("Credentials", "Server, username and password are required.")
            return

        try:
            date_str = self.sched_date_entry.get().strip()
            time_str = self.sched_time_entry.get().strip()
            run_at = datetime.strptime(f"{date_str} {time_str}", "%Y-%m-%d %H:%M")
        except ValueError:
            messagebox.showwarning("Schedule", "Invalid date/time format. Use YYYY-MM-DD and HH:MM.")
            return

        if run_at <= datetime.now():
            messagebox.showwarning("Schedule", "Scheduled time must be in the future.")
            return

        try:
            batch_size = max(1, int(self.batch_size_entry.get()))
            delay = max(0, float(self.delay_entry.get()))
        except ValueError:
            messagebox.showwarning("Settings", "Batch size and delay must be numbers.")
            return

        payload = {
            "creds": vars(creds),
            "recipients": [{"email": r["email"], "name": r["name"],
                            "attachment_path": r.get("attachment_path", "")} for r in recipients],
            "subject": subject,
            "body": body,
            "is_html": self.mode_var.get() == "html",
            "attachments": list(self.attachments),
            "batch_size": batch_size,
            "delay": delay,
        }
        job_id = self.scheduler.schedule_job(run_at, payload)
        messagebox.showinfo("Scheduled", f"Job {job_id} scheduled for {run_at}.\n\n"
                             "Note: the app must remain running (or be restarted before that "
                             "time) for the scheduled send to fire.")
        logger.info(f"Queued scheduled job {job_id} for {run_at} ({len(recipients)} recipients)")

    def _run_scheduled_job(self, payload):
        """Runs on the scheduler's background thread when a job fires."""
        creds = SmtpCredentials(**payload["creds"])
        sender = EmailSender(creds)
        recipients = payload["recipients"]
        try:
            sent, failed = sender.send_batches(
                recipients, payload["subject"], payload["body"], payload["is_html"],
                payload["attachments"], payload["batch_size"], payload["delay"],
                self.mailing_list, dry_run=False,
            )
            self.root.after(0, self._refresh_tree)
            logger.info(f"Scheduled job complete: sent={sent}, failed={len(failed)}")
        except Exception as e:
            logger.error(f"Scheduled job execution failed: {e}")

    def _on_close(self):
        self.mailing_list.save()
        self.root.destroy()


def main():
    root = tk.Tk()
    try:
        style = ttk.Style()
        if "clam" in style.theme_names():
            style.theme_use("clam")
    except Exception:
        pass
    app = BulkMailerApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
