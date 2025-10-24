#!/usr/bin/env python3
import argparse
import asyncio
import aiohttp
import json
import html
import hashlib
import logging
import os
import random
import re
import time
from collections import deque, OrderedDict
from typing import Optional, Dict, Any, List

import websockets
from bs4 import BeautifulSoup
import discord
from discord.ext import commands
from dotenv import load_dotenv

# -----------------------------
# Constants
INACTIVITY_CHECK_INTERVAL = 300  # 5-minute idle heartbeat
# -----------------------------
PROCESSED_CACHE_SIZE = 250        # sliding cache for processed sneed ids
# seconds to match Sneed echo with outbound Discord message
OUTBOUND_MATCH_WINDOW = 60
COOKIE_REFRESH_INTERVAL = 4 * 60 * 60  # 4 hours
OUTAGE_UPDATE_INTERVAL = 10       # outage embed update interval in seconds
QUEUED_MESSAGE_TTL = 90           # seconds before queued message is abandoned
MAX_ATTACHMENTS = 4               # refuse > 4 attachments
LITTERBOX_TTL = "72h"             # 72 hours

# Memory management constants
MAPPING_CACHE_SIZE = 1000          # Max message ID mappings to keep
MAPPING_CLEANUP_INTERVAL = 300     # Cleanup every 5 minutes
# MAPPING_MAX_AGE removed (size-bounded only)

# Outage tracking constants
OUTAGE_CLEANUP_DELAY = 120         # Delete outage message 2 minutes after reconnect
OUTAGE_INSTABILITY_WINDOW = 600    # 10 minute window for tracking outages
OUTAGE_INSTABILITY_THRESHOLD = 5   # 5+ outages = unstable

# CLI / env
# -----------------------------
parser = argparse.ArgumentParser(description="Sneedchat ↔ Discord Bridge")
parser.add_argument(
    "--debug",
    action="store_true",
    help="Enable debug logging")
parser.add_argument("--env", type=str, default=".env",
                    help="Path to .env file (default: .env)")
args = parser.parse_args()
load_dotenv(args.env)

# -----------------------------
# Logging
# -----------------------------
handlers = [logging.StreamHandler()]
if os.getenv("ENABLE_FILE_LOGGING", "false").lower() == "true":
    handlers.append(logging.FileHandler("bridge.log"))
logging.basicConfig(
    level=logging.DEBUG if args.debug else logging.INFO,
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    handlers=handlers
)
logger = logging.getLogger(__name__)

if args.debug:
    logger.debug("Debug mode enabled")
    logging.getLogger("websockets.client").setLevel(logging.INFO)
    logging.getLogger("websockets.protocol").setLevel(logging.INFO)

# -----------------------------
# Required env vars (match existing names)
# -----------------------------
REQUIRED_ENV_VARS = [
    "DISCORD_BOT_TOKEN",
    "DISCORD_CHANNEL_ID",
    "DISCORD_GUILD_ID",
    "DISCORD_WEBHOOK_URL",
    "SNEEDCHAT_ROOM_ID",
    "BRIDGE_USERNAME",
    "BRIDGE_PASSWORD"
]
for v in REQUIRED_ENV_VARS:
    if not os.getenv(v):
        raise ValueError(f"Required environment variable {v} is not set")

DISCORD_BOT_TOKEN = os.getenv("DISCORD_BOT_TOKEN")
DISCORD_CHANNEL_ID = int(os.getenv("DISCORD_CHANNEL_ID"))
DISCORD_GUILD_ID = int(os.getenv("DISCORD_GUILD_ID"))
DISCORD_WEBHOOK_URL = os.getenv("DISCORD_WEBHOOK_URL")
SNEEDCHAT_ROOM_ID = int(os.getenv("SNEEDCHAT_ROOM_ID"))

BRIDGE_USERNAME = os.getenv("BRIDGE_USERNAME")
BRIDGE_PASSWORD = os.getenv("BRIDGE_PASSWORD")

BRIDGE_USER_ID = os.getenv("BRIDGE_USER_ID")
if BRIDGE_USER_ID:
    BRIDGE_USER_ID = int(BRIDGE_USER_ID)

DISCORD_PING_USER_ID = os.getenv("DISCORD_PING_USER_ID")
if DISCORD_PING_USER_ID:
    try:
        DISCORD_PING_USER_ID = int(DISCORD_PING_USER_ID)
    except BaseException:
        DISCORD_PING_USER_ID = None

RECONNECT_INTERVAL = int(os.getenv("RECONNECT_INTERVAL", 7))
ENABLE_FILE_LOGGING = os.getenv(
    "ENABLE_FILE_LOGGING",
    "false").lower() == "true"

logger.info(f"Using .env file: {args.env}")
logger.info(f"Using Sneedchat room ID: {SNEEDCHAT_ROOM_ID}")
logger.info(f"Bridge username: {BRIDGE_USERNAME}")
if BRIDGE_USER_ID:
    logger.info(f"Bridge user filtering enabled - ID: {BRIDGE_USER_ID}")
logger.info(
    f"File logging: {
        'enabled' if ENABLE_FILE_LOGGING else 'disabled'}")

# -----------------------------
# BBCode -> Markdown parser
# -----------------------------


def bbcode_to_markdown(text: str) -> str:
    if not text:
        return ""
    # Normalize CRLF
    text = text.replace("\r\n", "\n").replace("\r", "\n")

    # Basic replacements (case-insensitive, DOTALL)
    text = re.sub(
        r'\[img\](.*?)\[/img\]',
        r'\1',
        text,
        flags=re.IGNORECASE | re.DOTALL)
    text = re.sub(r'\[video\](.*?)\[/video\]', r'\1',
                  text, flags=re.IGNORECASE | re.DOTALL)

    # [url=link]text[/url] -> [text](link) unless text is itself a link
    def _url_replace(m):
        link = m.group(1).strip()
        txt = m.group(2).strip()
        if re.match(r'^https?://', txt, re.IGNORECASE):
            return txt
        return f'[{txt}]({link})'
    text = re.sub(
        r'\[url=(.*?)\](.*?)\[/url\]',
        _url_replace,
        text,
        flags=re.IGNORECASE | re.DOTALL)

    # [url]link[/url] -> link
    text = re.sub(
        r'\[url\](.*?)\[/url\]',
        r'\1',
        text,
        flags=re.IGNORECASE | re.DOTALL)

    # Bold/italic/underline/strike (handle nested)
    text = re.sub(r'\[(?:b|strong)\](.*?)\[/\s*(?:b|strong)\]',
                  r'**\1**', text, flags=re.IGNORECASE | re.DOTALL)
    text = re.sub(
        r'\[(?:i|em)\](.*?)\[/\s*(?:i|em)\]',
        r'*\1*',
        text,
        flags=re.IGNORECASE | re.DOTALL)
    text = re.sub(r'\[(?:u)\](.*?)\[/\s*u\]', r'__\1__',
                  text, flags=re.IGNORECASE | re.DOTALL)
    text = re.sub(r'\[(?:s|strike)\](.*?)\[/\s*(?:s|strike)\]',
                  r'~~\1~~', text, flags=re.IGNORECASE | re.DOTALL)

    # Code & code blocks
    text = re.sub(r'\[code\](.*?)\[/code\]', r'`\1`',
                  text, flags=re.IGNORECASE | re.DOTALL)
    text = re.sub(
        r'\[(?:php|plain|code=\w+)\](.*?)\[/(?:php|plain|code)\]',
        r'```\1```',
        text,
        flags=re.IGNORECASE | re.DOTALL)

    # Quote blocks
    def _quote(m):
        inner = m.group(1).strip()
        return '\n'.join('> ' + line for line in inner.splitlines())
    text = re.sub(r'\[quote\](.*?)\[/quote\]', _quote,
                  text, flags=re.IGNORECASE | re.DOTALL)

    def _quote_attr(m):
        who = m.group(1).strip()
        inner = m.group(2).strip()
        header = f'> **{who} said:**'
        lines = '\n'.join('> ' + line for line in inner.splitlines())
        return header + '\n' + lines
    text = re.sub(
        r'\[quote=["\']?(.*?)["\']?\](.*?)\[/quote\]',
        _quote_attr,
        text,
        flags=re.IGNORECASE | re.DOTALL)

    # Spoilers
    text = re.sub(r'\[spoiler\](.*?)\[/spoiler\]', r'||\1||',
                  text, flags=re.IGNORECASE | re.DOTALL)

    # Color/size - strip tags but keep content
    text = re.sub(
        r'\[(?:color|size)=.*?\](.*?)\[/\s*(?:color|size)\]',
        r'\1',
        text,
        flags=re.IGNORECASE | re.DOTALL)

    # Lists & bullets
    text = re.sub(r'^\[\*\]\s*', '• ', text, flags=re.MULTILINE)
    text = re.sub(r'\[/?list\]', '', text, flags=re.IGNORECASE)

    # Remove unknown tags but leave content (for forgiving behavior)
    # This strips any [tag] or [/tag] style constructs left
    text = re.sub(r'\[/?[A-Za-z0-9\-=_]+\]', '', text)

    return text.strip()

# -----------------------------
# Bounded Mapping Dictionary (Memory Management)
# -----------------------------


class BoundedMappingDict:
    def __init__(self, maxsize: int = 1000):
        self.maxsize = maxsize
        self.data = OrderedDict()

    def __setitem__(self, key, value):
        if key in self.data:
            self.data.move_to_end(key)
        else:
            self.data[key] = value
            if len(self.data) > self.maxsize:
                self.data.popitem(last=False)

    def __getitem__(self, key):
        if key in self.data:
            self.data.move_to_end(key)
        return self.data[key]

    def get(self, key, default=None):
        try:
            return self[key]
        except KeyError:
            return default

    def pop(self, key, default=None):
        return self.data.pop(key, default)

    def __contains__(self, key):
        return key in self.data

    def cleanup_old_entries(self) -> int:
        removed = 0
        while len(self.data) > self.maxsize:
            self.data.popitem(last=False)
            removed += 1
        return removed

    def __len__(self):
        return len(self.data)


class CookieRefreshService:
    """Automatic cookie fetching and refresh service"""

    def __init__(self, username: str, password: str, domain: str = "kiwifarms.st"):
        self.username = username
        self.password = password
        self.domain = domain
        self.current_cookie: Optional[str] = None
        self.cookie_ready = asyncio.Event()
        self.refresh_task: Optional[asyncio.Task] = None
        self.shutdown_event = asyncio.Event()

    async def get_clearance_token(self, session: aiohttp.ClientSession) -> str:
        try:
            url = f"https://{self.domain}/"
            async with session.get(url) as response:
                html_text = await response.text()
            soup = BeautifulSoup(html_text, 'html.parser')
            challenge_element = soup.find('html', {'id': 'sssg'})
            if not challenge_element:
                logger.debug("No KiwiFlare challenge required")
                return ""
            salt = challenge_element.get('data-sssg-challenge')
            difficulty = int(challenge_element.get('data-sssg-difficulty', 0))
            if not salt or difficulty == 0:
                return ""
            logger.info(
                f"Solving KiwiFlare challenge (difficulty={difficulty})")
            nonce = random.randint(0, 2**63 - 1)
            attempts = 0
            max_attempts = 10_000_000
            while attempts < max_attempts:
                nonce += 1
                attempts += 1
                input_string = f"{salt}{nonce}"
                hash_result = hashlib.sha256(
                    input_string.encode('utf-8')).digest()
                required_bytes = difficulty // 8
                required_bits = difficulty % 8
                valid = True
                for i in range(required_bytes):
                    if hash_result[i] != 0:
                        valid = False
                        break
                if valid and required_bits > 0 and required_bytes < len(
                        hash_result):
                    byte_val = hash_result[required_bytes]
                    mask = 0xFF << (8 - required_bits)
                    if byte_val & mask != 0:
                        valid = False
                if valid:
                    submit_url = f"https://{self.domain}/.sssg/api/answer"
                    data = {'a': salt, 'b': str(nonce)}
                    async with session.post(submit_url, data=data) as submit_response:
                        result = await submit_response.json()
                    if 'auth' in result:
                        token = result['auth']
                        session.cookie_jar.update_cookies(
                            {'sssg_clearance': token}, response_url=url)
                        return token
            logger.warning("Failed to solve challenge within attempt limit")
            return ""
        except Exception as e:
            logger.error(f"Clearance token error: {e}")
            return ""

    async def fetch_fresh_cookie(self) -> Optional[str]:
        try:
            async with aiohttp.ClientSession(headers={'User-Agent': 'Mozilla/5.0'}) as session:
                await self.get_clearance_token(session)
                login_url = f"https://{self.domain}/login"
                async with session.get(login_url) as response:
                    html_text = await response.text()
                soup = BeautifulSoup(html_text, 'html.parser')
                html_element = soup.find('html')
                if not html_element:
                    logger.error("❌ Could not parse login page")
                    return None
                csrf_token = html_element.get('data-csrf')
                if not csrf_token:
                    logger.error("❌ Could not find CSRF token")
                    return None
                login_data = {
                    '_xfToken': csrf_token,
                    'login': self.username,
                    'password': self.password,
                    '_xfRedirect': f'https://{self.domain}/',
                    'remember': '1'
                }
                post_url = f"https://{self.domain}/login/login"
                async with session.post(post_url, data=login_data, allow_redirects=False) as response:
                    auth_cookies = []
                    cookie_names = [
                        'xf_user',
                        'xf_toggle',
                        'xf_csrf',
                        'xf_session',
                        'sssg_clearance']
                    for cookie in session.cookie_jar:
                        if cookie.key in cookie_names and cookie.value:
                            auth_cookies.append(f"{cookie.key}={cookie.value}")
                    if not auth_cookies:
                        logger.error("❌ Login failed: no cookies received")
                        return None
                    cookie_string = "; ".join(auth_cookies)
                    logger.info(
                        f"✅ Successfully fetched fresh cookie ({
                            len(auth_cookies)} tokens)")
                    return cookie_string
        except Exception as e:
            logger.error(f"❌ Failed to fetch fresh cookie: {e}")
            return None

    async def refresh_loop(self):
        try:
            logger.info("🔒 Fetching initial cookie...")
            fresh_cookie = await self.fetch_fresh_cookie()
            if fresh_cookie:
                self.current_cookie = fresh_cookie
                self.cookie_ready.set()
                logger.info("✅ Initial cookie acquired, bridge can start")
            else:
                logger.error(
                    "❌ Failed to acquire initial cookie, cannot start bridge")
                return
            while not self.shutdown_event.is_set():
                try:
                    await asyncio.wait_for(self.shutdown_event.wait(), timeout=COOKIE_REFRESH_INTERVAL)
                    break
                except asyncio.TimeoutError:
                    pass
                logger.info("🔄 Starting automatic cookie refresh (interval)")
                fresh_cookie = await self.fetch_fresh_cookie()
                if fresh_cookie:
                    self.current_cookie = fresh_cookie
                    logger.info("✅ Cookie refresh completed successfully")
                else:
                    logger.warning(
                        "⚠️ Cookie refresh failed, keeping existing cookie")
        except Exception as e:
            logger.error(f"❌ Cookie refresh loop error: {e}")

    async def start(self):
        logger.info("Starting cookie refresh service")
        self.refresh_task = asyncio.create_task(self.refresh_loop())

    async def wait_for_cookie(self):
        await self.cookie_ready.wait()

    async def stop(self):
        self.shutdown_event.set()
        if self.refresh_task and not self.refresh_task.done():
            self.refresh_task.cancel()
            try:
                await self.refresh_task
            except asyncio.CancelledError:
                pass

    def get_current_cookie(self) -> Optional[str]:
        return self.current_cookie

# -----------------------------
# SneedChatClient
# -----------------------------


class SneedChatClient:
    def __init__(
            self,
            cookie: str,
            room_id: int = 16,
            reconnect_interval: int = 7,
            cookie_service: Optional[CookieRefreshService] = None):
        self.ws_url = "wss://kiwifarms.st:9443/chat.ws"
        self.cookie = cookie
        self.cookie_service = cookie_service
        self.room_id = room_id
        self.ws: Optional[websockets.client.WebSocketClientProtocol] = None
        self.connected = False
        # auth/health tracking
        self.authenticated = False
        self.awaiting_auth = False
        self.auth_deadline = 0
        self.last_inbound_activity = time.time()
        self.last_outbound_echo = 0
        self.integrity_task: Optional[asyncio.Task] = None

        self.last_message_time = time.time()
        self.read_task: Optional[asyncio.Task] = None
        self.write_task: Optional[asyncio.Task] = None
        self.heartbeat_task: Optional[asyncio.Task] = None
        self.cleanup_task: Optional[asyncio.Task] = None
        self.write_queue = asyncio.Queue()
        self.shutdown_event = asyncio.Event()
        self.reconnect_interval = reconnect_interval

        # callbacks assigned by DiscordBridge
        self.on_message = None
        self.on_edit = None
        self.on_delete = None
        self.on_connect = None
        self.on_disconnect = None

        # dedupe / edit tracking
        self.processed_message_ids = deque(maxlen=PROCESSED_CACHE_SIZE)
        self.message_edit_dates = BoundedMappingDict(
            maxsize=MAPPING_CACHE_SIZE
        )

        # reconnection attempts counter
        self.reconnect_attempts = 0

        # helper overrides (injected by DiscordBridge)
        self._recent_outbound_iter = lambda: []
        self._map_discord_sneed = lambda discord_id, sneed_id, username: None

    async def cleanup_loop(self):
        """Periodic cleanup of old mappings"""
        try:
            while not self.shutdown_event.is_set():
                await asyncio.sleep(MAPPING_CLEANUP_INTERVAL)

                # Cleanup edit dates
                removed = self.message_edit_dates.cleanup_old_entries()
                if removed > 0:
                    logger.info(
                        f"🧹 Cleaned up {removed} old message edit tracking entries")

        except asyncio.CancelledError:
            logger.debug("Cleanup task cancelled")
        except Exception as e:
            logger.error(f"Cleanup loop error: {e}")

    async def connect(self) -> bool:
        if self.connected:
            return True
        if self.cookie_service:
            fresh_cookie = self.cookie_service.get_current_cookie()
            if fresh_cookie:
                logger.debug("Using refreshed cookie for connection")
                self.cookie = fresh_cookie
        headers = {"Cookie": self.cookie}
        try:
            logger.info(
                f"Connecting to Sneedchat room {
                    self.room_id} (attempting websocket)")
            self.ws = await websockets.connect(self.ws_url, additional_headers=headers, ping_interval=20, ping_timeout=10)
            self.connected = True
            self.reconnect_attempts = 0
            self.read_task = asyncio.create_task(self.read_loop())
            self.write_task = asyncio.create_task(self.write_loop())
            self.heartbeat_task = asyncio.create_task(self.heartbeat_loop())
            self.cleanup_task = asyncio.create_task(self.cleanup_loop())
            await self.send_command(f"/join {self.room_id}")
            logger.info(
                f"✅ Successfully connected to Sneedchat room {
                    self.room_id}")
            # begin authentication verification window + heartbeat
            self.authenticated = False
            self.awaiting_auth = True
            self.auth_deadline = time.time() + 10
            try:
                self.integrity_task.cancel()
            except Exception:
                pass
            self.integrity_task = asyncio.create_task(self.integrity_loop())
            if self.on_connect:
                await self.on_connect()
            return True
        except Exception as e:
            logger.error(f"Sneedchat connection failed: {e}")
            await self.handle_disconnect()
            return False

    async def disconnect(self):
        logger.info("Disconnecting from Sneedchat")
        self.shutdown_event.set()
        self.connected = False
        for task in (
                self.read_task,
                self.write_task,
                self.heartbeat_task,
                self.cleanup_task):
            if task and not task.done():
                task.cancel()
                try:
                    await task
                except asyncio.CancelledError:
                    pass
        if self.ws:
            try:
                await self.ws.close()
            except Exception:
                pass
            self.ws = None

    async def read_loop(self):
        try:
            async for message in self.ws:
                if self.shutdown_event.is_set():
                    break
                self.last_message_time = time.time()
                self.last_inbound_activity = time.time()
                if self.awaiting_auth and not self.authenticated:
                    if self._check_for_user_in_userlist(message):
                        self.authenticated = True
                        self.awaiting_auth = False
                        logger.info(
                            "✅ Authentication verified via userlist payload")
                    elif time.time() > self.auth_deadline:
                        logger.warning(
                            "🔒 Auth verification window expired; reconnecting with fresh cookie")
                        await self.handle_disconnect()
                        break
                    continue
                await self.handle_message(message)
        except Exception as e:
            logger.error(f"Sneedchat read loop error: {e}")
        finally:
            if not self.shutdown_event.is_set():
                await self.handle_disconnect()

    async def write_loop(self):
        try:
            while not self.shutdown_event.is_set():
                try:
                    msg = await asyncio.wait_for(self.write_queue.get(), timeout=1.0)
                    if self.ws and self.connected:
                        logger.debug(f"➡️ Sending to Sneedchat: {msg}")
                        await self.ws.send(msg)
                except asyncio.TimeoutError:
                    continue
        except Exception as e:
            logger.error(f"Sneedchat write loop error: {e}")
        finally:
            if not self.shutdown_event.is_set():
                await self.handle_disconnect()

    async def integrity_loop(self):
        try:
            while not self.shutdown_event.is_set():
                await asyncio.sleep(INACTIVITY_CHECK_INTERVAL)
                if not self.connected:
                    continue
                now = time.time()
                # Skip if recent inbound, echo, or queue non-empty
                if (now - self.last_inbound_activity) < INACTIVITY_CHECK_INTERVAL:
                    continue
                if self.last_outbound_echo and (
                        now - self.last_outbound_echo) < INACTIVITY_CHECK_INTERVAL:
                    continue
                if hasattr(
                        self, "write_queue") and not self.write_queue.empty():
                    continue
                logger.info("💤 Idle ≥5m → issuing /join heartbeat")
                await self.send_command(f"/join {self.room_id}")
                self.awaiting_auth = True
                self.auth_deadline = time.time() + 10
        except asyncio.CancelledError:
            pass
        except Exception as e:
            logger.error(f"Integrity loop error: {e}")

    async def heartbeat_loop(self):
        try:
            while not self.shutdown_event.is_set():
                await asyncio.sleep(30)
                if self.connected and time.time() - self.last_message_time > 60:
                    await self.send_command("/ping")
        except Exception as e:
            logger.error(f"Heartbeat error: {e}")

    def _check_for_user_in_userlist(self, raw: str) -> bool:
        try:
            data = json.loads(raw)
        except Exception:
            return False
        users = data.get("users")
        if not users:
            return False
        if 'BRIDGE_USER_ID' in globals() and BRIDGE_USER_ID and str(BRIDGE_USER_ID) in users:
            return True
        uname = (
            globals().get('BRIDGE_USERNAME') or '').strip().lower()
        for u in users.values():
            if u.get("username", "").strip().lower() == uname and uname:
                return True
        return False

    async def handle_message(self, raw: str):
        # debug full payload if requested
        if args.debug:
            try:
                parsed = json.loads(raw)
                logger.debug("=== Full Sneedchat Payload ===")
                logger.debug(json.dumps(parsed, indent=2))
            except Exception:
                logger.debug(f"📨 Raw non-JSON data: {raw}")

        try:
            content = json.loads(raw)
        except json.JSONDecodeError:
            return

        # top-level deletes
        if "delete" in content:
            delete_field = content["delete"]
            del_list = delete_field if isinstance(
                delete_field, list) else [delete_field]
            for did in del_list:
                try:
                    did_int = int(did)
                except Exception:
                    continue
                logger.info(
                    f"🗑️ Received top-level Sneed delete for id={did_int}")
                self.message_edit_dates.pop(did_int, None)
                try:
                    if did_int in self.processed_message_ids:
                        self.processed_message_ids.remove(did_int)
                except Exception:
                    pass
                if self.on_delete:
                    try:
                        await self.on_delete(did_int)
                    except Exception as e:
                        logger.error(
                            f"Error in on_delete callback for id={did_int}: {e}")

        messages = []
        if "messages" in content:
            messages = content["messages"]
        elif "message" in content:
            messages = [content["message"]]

        for msg in messages:
            try:
                author = msg.get("author", {}) or {}
                username = author.get("username", "Unknown")
                user_id = author.get("id")
                message_id = msg.get("message_id")
                message_text = msg.get(
                    "message_raw") or msg.get("message") or ""
                message_text = html.unescape(message_text)
                edit_date = int(msg.get("message_edit_date", 0) or 0)
                deleted_flag = msg.get("deleted") or msg.get(
                    "is_deleted") or False

                # message-scoped deletion
                if deleted_flag:
                    logger.info(
                        f"🗑️ Sneed message-scoped deletion id={message_id}")
                    if message_id:
                        self.message_edit_dates.pop(message_id, None)
                        try:
                            if message_id in self.processed_message_ids:
                                self.processed_message_ids.remove(message_id)
                        except Exception:
                            pass
                    if self.on_delete:
                        await self.on_delete(message_id)
                    continue

                # If message is from the bridge user: attempt mapping but do
                # not forward
                if (BRIDGE_USER_ID and user_id == BRIDGE_USER_ID) or (
                        BRIDGE_USERNAME and username == BRIDGE_USERNAME):
                    logger.debug(
                        f"🚫 Received bridge-user echo from Sneed id={message_id}; attempting mapping but not forwarding")
                    if message_id:
                        now = time.time()
                        matched_entry = None
                        for entry in reversed(
                                list(self._recent_outbound_iter())):
                            if entry.get("mapped"):
                                continue
                            if entry.get("content") == message_text and (
                                    now - entry.get("ts", 0)) <= OUTBOUND_MATCH_WINDOW:
                                matched_entry = entry
                                break
                        if matched_entry:
                            discord_id = matched_entry["discord_id"]
                            self._map_discord_sneed(
                                discord_id, int(message_id), username)
                            matched_entry["mapped"] = True
                            self.last_outbound_echo = time.time()
                            logger.debug(
                                f"Mapped Discord->{message_id} (discord_id={discord_id}) via bridge echo")
                    if message_id:
                        self.processed_message_ids.append(message_id)
                        self.message_edit_dates[message_id] = edit_date
                    # DO NOT forward to Discord
                    continue

                # Dedup / edit detection
                if message_id and message_id in self.processed_message_ids:
                    prev_edit = self.message_edit_dates.get(message_id, 0)
                    if edit_date and edit_date > prev_edit:
                        logger.info(
                            f"✏️ Edit detected for sneed_id={message_id}")
                        self.message_edit_dates[message_id] = edit_date
                        if self.on_edit:
                            await self.on_edit(message_id, message_text)
                    else:
                        logger.debug(
                            f"🔄 Skipping duplicate message ID {message_id} from {username}")
                    continue

                # New message
                logger.info(
                    f"📄 New Sneed message from {username}: {message_text[:120]}...")
                if message_id:
                    self.processed_message_ids.append(message_id)
                    self.message_edit_dates[message_id] = edit_date

                if self.on_message:
                    await self.on_message({
                        "username": username,
                        "content": message_text,
                        "raw": msg,
                        "message_id": message_id,
                        "author_id": user_id
                    })
            except Exception as e:
                logger.error(f"Error processing Sneed message: {e}")

    def _recent_outbound_iter(self):
        return []

    def _map_discord_sneed(
            self,
            discord_id: int,
            sneed_id: int,
            username: str):
        pass

    async def send_message(self, content: str) -> bool:
        """Send a plain message to sneed via websocket queue. Return True if queued for send,
           False if not connected (caller should queue)."""
        if not self.connected or not self.ws:
            logger.warning("Cannot send to Sneedchat: not connected")
            return False
        await self.write_queue.put(content)
        logger.debug("Queued message for Sneedchat websocket send")
        return True

    async def send_command(self, command: str):
        if not self.connected or not self.ws:
            logger.warning("Cannot send command to Sneedchat: not connected")
            return
        await self.write_queue.put(command)

    async def handle_disconnect(self):
        if self.shutdown_event.is_set():
            return
        try:
            self.reconnect_attempts = getattr(
                self, "reconnect_attempts", 0) + 1
        except Exception:
            self.reconnect_attempts = 1
        self.connected = False
        logger.warning("🔴 Sneedchat disconnected")
        if self.on_disconnect:
            await self.on_disconnect()
        await asyncio.sleep(self.reconnect_interval)
        await self.connect()

# -----------------------------
# Discord Bridge
# -----------------------------


class DiscordBridge:
    def __init__(self, sneed_client: SneedChatClient):
        intents = discord.Intents.default()
        intents.message_content = True
        self.bot = commands.Bot(command_prefix="!", intents=intents)
        self.sneed_client = sneed_client

        # hook callbacks
        self.sneed_client.on_message = self.on_sneed_message
        self.sneed_client.on_edit = self._handle_sneed_edit
        self.sneed_client.on_delete = self._handle_sneed_delete
        self.sneed_client.on_connect = self.on_sneed_connect
        self.sneed_client.on_disconnect = self.on_sneed_disconnect

        # provide sneed client with mapping helpers
        self.sneed_client._recent_outbound_iter = self._recent_outbound_iter
        self.sneed_client._map_discord_sneed = self._map_discord_sneed

        self.session: Optional[aiohttp.ClientSession] = None

        # mapping tables (now with memory management)
        self.sneed_to_discord = BoundedMappingDict(
            maxsize=MAPPING_CACHE_SIZE
        )
        self.discord_to_sneed = BoundedMappingDict(
            maxsize=MAPPING_CACHE_SIZE
        )
        self.sneed_usernames = BoundedMappingDict(
            maxsize=MAPPING_CACHE_SIZE
        )

        # recent outbound messages (Discord -> Sneed) awaiting echo mapping
        self.recent_outbound = deque(maxlen=PROCESSED_CACHE_SIZE)

        # queued outbound messages when Sneedchat is down (older than TTL
        # dropped)
        # {content, channel_id, ts, discord_id}
        self.queued_outbound: List[Dict[str, Any]] = []

        # outage tracking
        self.outage_message: Optional[Any] = None
        self.outage_start: Optional[float] = None
        self.outage_task: Optional[asyncio.Task] = None
        self.cleanup_task: Optional[asyncio.Task] = None
        self.outage_cleanup_task: Optional[asyncio.Task] = None

        # outage event history (for instability detection)
        self.outage_events: List[float] = []  # timestamps of outages

        self.shutdown_event = asyncio.Event()

        # start bot handlers
        self.setup_bot()

    async def cleanup_loop(self):
        """Periodic cleanup of old mappings and queued messages"""
        try:
            while not self.shutdown_event.is_set():
                await asyncio.sleep(MAPPING_CLEANUP_INTERVAL)

                # Cleanup mapping dictionaries
                removed_s2d = self.sneed_to_discord.cleanup_old_entries()
                removed_d2s = self.discord_to_sneed.cleanup_old_entries()
                removed_usernames = self.sneed_usernames.cleanup_old_entries()

                total_removed = removed_s2d + removed_d2s + removed_usernames
                if total_removed > 0:
                    logger.info(
                        f"🧹 Cleaned up {total_removed} old message mappings")

                # Cleanup expired queued messages
                now = time.time()
                before_count = len(self.queued_outbound)
                self.queued_outbound = [
                    msg for msg in self.queued_outbound
                    if now - msg.get("ts", now) <= QUEUED_MESSAGE_TTL
                ]
                after_count = len(self.queued_outbound)
                if before_count > after_count:
                    logger.info(
                        f"🧹 Removed {
                            before_count -
                            after_count} expired queued messages")

        except asyncio.CancelledError:
            logger.debug("Bridge cleanup task cancelled")
        except Exception as e:
            logger.error(f"Bridge cleanup loop error: {e}")

    def _get_outage_stats(self) -> Dict[str, Any]:
        """Get outage statistics for the last 10 minutes"""
        now = time.time()
        window_start = now - OUTAGE_INSTABILITY_WINDOW

        # Filter outage events within the window
        recent_outages = [
            ts for ts in self.outage_events if ts >= window_start]

        # Calculate total downtime (approximate: assume each outage lasted
        # until next event or now)
        total_downtime = 0
        for i, ts in enumerate(recent_outages):
            if i + 1 < len(recent_outages):
                total_downtime += recent_outages[i + 1] - ts
            else:
                # Last outage - only count if still ongoing
                if not self.sneed_client.connected:
                    total_downtime += now - ts

        return {
            "count": len(recent_outages),
            "total_downtime": total_downtime,
            "is_unstable": len(recent_outages) >= OUTAGE_INSTABILITY_THRESHOLD
        }

    async def _delete_old_outage_messages(self):
        """Delete all old outage messages from the channel"""
        try:
            channel = self.bot.get_channel(DISCORD_CHANNEL_ID)
            if not channel:
                return

            # Fetch recent messages and find outage notices
            async for message in channel.history(limit=100):
                if message.author == self.bot.user and message.embeds:
                    embed = message.embeds[0]
                    if embed.title == "🌉 Bridge Status":
                        await message.delete()
                        logger.debug(
                            f"Deleted old outage message id={
                                message.id}")
        except Exception as e:
            logger.debug(
                f"Could not delete old outage messages: {e}")

    async def _schedule_outage_cleanup(self):
        """Schedule deletion of outage message 2 minutes after reconnect"""
        if self.outage_cleanup_task and not self.outage_cleanup_task.done():
            self.outage_cleanup_task.cancel()
            try:
                await self.outage_cleanup_task
            except asyncio.CancelledError:
                pass

        async def cleanup_after_delay():
            try:
                await asyncio.sleep(OUTAGE_CLEANUP_DELAY)
                if self.outage_message:
                    try:
                        if isinstance(self.outage_message, discord.Message):
                            await self.outage_message.delete()
                        else:
                            webhook = discord.Webhook.from_url(
                                DISCORD_WEBHOOK_URL, session=self.session)
                            await webhook.delete_message(getattr(self.outage_message, "id", self.outage_message))
                        logger.info(
                            "🗑️ Deleted outage message after 2 minute delay")
                    except Exception as e:
                        logger.debug(f"Could not delete outage message: {e}")
                    finally:
                        self.outage_message = None
                        self.outage_start = None
            except asyncio.CancelledError:
                pass

        self.outage_cleanup_task = asyncio.create_task(cleanup_after_delay())

    def setup_bot(self):
        @self.bot.event
        async def on_ready():
            logger.info(
                f"🤖 Discord bot ready: {
                    self.bot.user} (id={
                        self.bot.user.id})")
            self.session = aiohttp.ClientSession()

            # Start cleanup task
            if not self.cleanup_task or self.cleanup_task.done():
                self.cleanup_task = asyncio.create_task(self.cleanup_loop())

            # ensure sneedclient connected
            if not self.sneed_client.connected:
                asyncio.create_task(self.sneed_client.connect())

        @self.bot.event
        async def on_message(message: discord.Message):
            # ignore bots
            if message.author.bot:
                return

            # commands
            if message.content.startswith("!"):
                await self.bot.process_commands(message)
                return

            if message.channel.id != DISCORD_CHANNEL_ID:
                return

            logger.info(
                f"📤 Discord → Sneedchat: {
                    message.author.display_name}: {
                        message.content}")
            await self.on_discord_message(message)

        @self.bot.event
        async def on_message_edit(
                before: discord.Message,
                after: discord.Message):
            try:
                discord_id = after.id
                if discord_id in self.discord_to_sneed:
                    sneed_id = self.discord_to_sneed[discord_id]
                    payload = json.dumps(
                        {"id": int(sneed_id), "message": after.content.strip()})
                    logger.info(
                        f"↩️ Discord edit -> Sneedchat (sneed_id={sneed_id})")
                    await self.sneed_client.send_command(f"/edit {payload}")
                else:
                    logger.debug(
                        f"No mapping for edited discord_id={discord_id}")
            except Exception as e:
                logger.error(f"Error handling discord edit: {e}")

        @self.bot.event
        async def on_message_delete(message: discord.Message):
            try:
                discord_id = message.id
                if discord_id in self.discord_to_sneed:
                    sneed_id = self.discord_to_sneed[discord_id]
                    logger.info(
                        f"↩️ Discord delete -> Sneedchat (sneed_id={sneed_id})")
                    await self.sneed_client.send_command(f"/delete {int(sneed_id)}")
                else:
                    logger.debug(
                        f"No mapping for deleted discord_id={discord_id}")
            except Exception as e:
                logger.error(f"Error handling discord delete: {e}")

        @self.bot.command(name="status")
        async def status_command(ctx):
            status = "🟢 Connected" if self.sneed_client.connected else "🔴 Disconnected"
            embed = discord.Embed(
                title="🌉 Bridge Status",
                description=f"**Sneedchat:** {status}\n**Room ID:** {self.sneed_client.room_id}",
                color=0x00FF00 if self.sneed_client.connected else 0xFF0000
            )
            await ctx.send(embed=embed)

        @self.bot.command(name="test")
        async def test_command(
                ctx, *, text: str = "This is a test from !test"):
            if not self.session:
                await ctx.send("❌ No HTTP session available for webhook.")
                return
            try:
                webhook = discord.Webhook.from_url(
                    DISCORD_WEBHOOK_URL, session=self.session)
                response = await webhook.send(content=text, username="SneedTestUser", wait=True)
                await ctx.send("✅ Test message sent via webhook.")
                if args.debug:
                    logger.debug(f"Webhook test response: {response}")
            except Exception as e:
                logger.error(f"❌ Test command webhook send failed: {e}")
                await ctx.send(f"❌ Failed: {e}")

    def _recent_outbound_iter(self):
        return list(self.recent_outbound)

    def _map_discord_sneed(
            self,
            discord_id: int,
            sneed_id: int,
            username: str):
        try:
            self.discord_to_sneed[int(discord_id)] = int(sneed_id)
            self.sneed_to_discord[int(sneed_id)] = int(discord_id)
            self.sneed_usernames[int(sneed_id)] = username
            if args.debug:
                logger.debug(
                    f"Mapped sneed_id={sneed_id} <-> discord_id={discord_id} (username='{username}')")
        except Exception as e:
            logger.error(f"Failed to create map discord->{sneed_id}: {e}")

    # -------- Attachment uploads -> litterbox --------
    async def upload_to_litterbox(
            self,
            file_url: str,
            filename: str) -> Optional[str]:
        """Download from Discord CDN and upload to Litterbox; return direct URL or None."""
        try:
            # Download from the provided URL (this will usually be discordcdn)
            async with self.session.get(file_url) as resp:
                if resp.status != 200:
                    logger.error(
                        f"Failed to download attachment '{filename}': HTTP {
                            resp.status}")
                    return None
                data = await resp.read()
            # Prepare form data
            form = aiohttp.FormData()
            # temporary: reqtype=fileupload, time=72h
            form.add_field('reqtype', 'fileupload')
            form.add_field('time', LITTERBOX_TTL)
            form.add_field('fileToUpload', data, filename=filename)
            async with self.session.post('https://litterbox.catbox.moe/resources/internals/api.php', data=form) as upl:
                if upl.status != 200:
                    logger.error(
                        f"Litterbox upload failed for '{filename}': HTTP {
                            upl.status}")
                    txt = await upl.text()
                    logger.debug(f"Litterbox response: {txt}")
                    return None
                url = (await upl.text()).strip()
                logger.info(
                    f"SUCCESS: Uploaded '{filename}' to Litterbox: {url}")
                return url
        except Exception as e:
            logger.error(
                f"Exception during Litterbox upload for '{filename}': {e}")
            return None

    async def format_attachment_bbcode(
            self, attachment: discord.Attachment) -> Optional[str]:
        """Upload attachment and return BBCode string for Sneedchat."""
        url = await self.upload_to_litterbox(attachment.url, attachment.filename)
        if not url:
            return None
        ctype = (attachment.content_type or "").lower()
        if ctype.startswith(
                'video/') or attachment.filename.lower().endswith(('.mp4', '.webm', '.mov', '.mkv')):
            # Use [url=link]Video N[/url]
            return url
        else:
            # For images, return url (Sneed will embed)
            return url

    # -------- Discord -> Sneed message handling --------
    async def on_discord_message(self, message: discord.Message):
        # If Sneedchat offline: queue message
        content_text = message.content.strip()
        # Handle reply mapping (Discord -> Sneed)
        if message.reference and getattr(
                message.reference, "message_id", None):
            ref_discord_id = message.reference.message_id
            try:
                sneed_id = self.discord_to_sneed.get(ref_discord_id)
                if sneed_id:
                    original_username = self.sneed_usernames.get(sneed_id)
                    if original_username:
                        # do NOT strip spaces from username per instruction;
                        # only strip message text
                        content_text = f"@{original_username}, {content_text}"
            except Exception as e:
                logger.error(f"Failed to resolve reply username mapping: {e}")

        # Attachments handling: limit and upload
        attachments_bb: List[str] = []
        if message.attachments:
            if len(message.attachments) > MAX_ATTACHMENTS:
                await message.channel.send(f"❌ Refusing to upload attachments: limit is {MAX_ATTACHMENTS}.")
                return
            # Upload each and produce BBCode lines
            for idx, att in enumerate(message.attachments[:MAX_ATTACHMENTS]):
                # Upload and get url
                catbox_url = await self.upload_to_litterbox(att.url, att.filename)
                if not catbox_url:
                    # error reporting in discord buffer
                    await message.channel.send(f"❌ Failed to upload attachment `{att.filename}` to Litterbox; aborting send.")
                    logger.error(
                        f"Attachment upload failed for {
                            att.filename}; aborting Discord->Sneed send.")
                    return
                # Build bbcode: video -> [url=..]Video N[/url], images ->
                # [url=..][img]..[/img][/url] per earlier spec
                content_type = (att.content_type or "").lower()
                if content_type.startswith('video') or att.filename.lower().endswith(
                        ('.mp4', '.webm', '.mov', '.mkv')):
                    attachments_bb.append(
                        f"[url={catbox_url}][video]{catbox_url}[/video][/url]")
                else:
                    attachments_bb.append(
                        f"[url={catbox_url}][img]{catbox_url}[/img][/url]")

        # Build final message to send to Sneed
        combined = content_text
        if attachments_bb:
            combined = combined + \
                ("\n" if combined else "") + "\n".join(attachments_bb)

        # Try to send to Sneedchat (non-blocking)
        sent = await self.sneed_client.send_message(combined)
        if sent:
            # record for outbound mapping waiting for echo (so bridge can map
            # sneed id to discord id)
            try:
                entry = {
                    "discord_id": message.id,
                    "content": combined,
                    "ts": time.time(),
                    "mapped": False
                }
                self.recent_outbound.append(entry)
                if args.debug:
                    logger.debug(
                        f"Queued outbound mapping for discord_id={
                            message.id}")
            except Exception as e:
                logger.error(f"Failed to record outbound mapping: {e}")
        else:
            # Not connected -> queue with timestamp and inform discord channel
            self.queued_outbound.append({
                "content": combined,
                "channel_id": message.channel.id,
                "ts": time.time(),
                "discord_id": message.id
            })
            logger.info(
                "Queued message for delivery when Sneedchat reconnects")
            try:
                # notify channel
                await message.channel.send(f"⚠️ Sneedchat appears offline. Your message has been queued for delivery (will expire after {QUEUED_MESSAGE_TTL}s).")
            except Exception:
                logger.debug("Failed sending queue-notice to channel")

    # -------- Sneedchat -> Discord handlers --------
    async def on_sneed_message(self, msg: Dict[str, Any]):
        username = msg.get("username")
        raw_content = msg.get("content")
        # Always parse through bbcode parser
        content = bbcode_to_markdown(raw_content)
        raw = msg.get("raw", {}) or {}
        message_id = raw.get("message_id")
        author_id = msg.get("author_id")

        # Replace mentions of BRIDGE_USERNAME with Discord ping (if configured)
        if BRIDGE_USERNAME and DISCORD_PING_USER_ID:
            try:
                pattern = re.compile(
                    rf'@{re.escape(BRIDGE_USERNAME)}(?=\W|$)', re.IGNORECASE)
                content = pattern.sub(f'<@{DISCORD_PING_USER_ID}>', content)
            except Exception:
                pass

        avatar_url = None
        author = raw.get("author", {}) or {}
        if author.get("avatar_url"):
            avatar_path = author["avatar_url"]
            avatar_url = f"https://kiwifarms.st{avatar_path}" if avatar_path.startswith(
                "/") else avatar_path

        # If this Sneed message is an echo of the bridge user -> attempt to map
        # to the outbound discord message, DO NOT forward
        if (author_id and BRIDGE_USER_ID and author_id == BRIDGE_USER_ID) or (
                BRIDGE_USERNAME and username == BRIDGE_USERNAME):
            if args.debug:
                logger.debug(
                    f"Bridge-echo from sneed_id={message_id} (username={username}); attempting mapping but not forwarding")
            if message_id:
                now = time.time()
                matched_entry = None
                for entry in list(self.recent_outbound):
                    if entry.get("mapped"):
                        continue
                    if entry.get("content") == (raw_content) and (
                            now - entry.get("ts", 0)) <= OUTBOUND_MATCH_WINDOW:
                        matched_entry = entry
                        break
                if matched_entry:
                    discord_id = matched_entry["discord_id"]
                    self._map_discord_sneed(
                        discord_id, int(message_id), username)
                    matched_entry["mapped"] = True
                    self.last_outbound_echo = time.time()
                    if args.debug:
                        logger.debug(
                            f"Mapped outbound discord_id={discord_id} -> sneed_id={message_id} (bridge echo)")
                    return
            if args.debug:
                logger.debug(
                    "No recent outbound match for bridge echo; dropping silently")
            return

        # Normal Sneed-origin message: post via webhook with parsed content
        if not self.session:
            logger.error("❌ No HTTP session for webhook operations")
            return

        try:
            webhook = discord.Webhook.from_url(
                DISCORD_WEBHOOK_URL, session=self.session)
            # send parsed content; username is verbatim from Sneed JSON
            sent = await webhook.send(content=content, username=username, avatar_url=avatar_url, wait=True)
            logger.info(f"✅ Sent Sneedchat → Discord: {username}")
            # map to track edits/deletes
            if message_id:
                discord_msg_id = None
                try:
                    # some webhook libs return an object, sometimes id
                    # directly; handle both
                    discord_msg_id = int(getattr(sent, "id", None) or sent)
                except Exception:
                    discord_msg_id = None
                if discord_msg_id:
                    self.sneed_to_discord[int(message_id)] = discord_msg_id
                    self.discord_to_sneed[discord_msg_id] = int(message_id)
                    self.sneed_usernames[int(message_id)] = username
                    if args.debug:
                        logger.debug(
                            f"Mapped Sneed->{discord_msg_id} (sneed_id={message_id})")
        except Exception as e:
            logger.error(
                f"❌ Failed to send Sneed → Discord webhook message: {e}")

    async def _handle_sneed_edit(
            self, sneed_id: int, new_content: str):
        try:
            sneed_id = int(sneed_id)
        except Exception:
            return
        discord_msg_id = self.sneed_to_discord.get(sneed_id)
        if not discord_msg_id:
            logger.debug(
                f"No discord mapping for sneed edit id={sneed_id}")
            return
        if not self.session:
            logger.error("❌ No HTTP session for webhook edit")
            return

        # run through parser BEFORE editing so bbcode isn't shown raw
        parsed = bbcode_to_markdown(new_content)
        webhook = discord.Webhook.from_url(
            DISCORD_WEBHOOK_URL, session=self.session)
        try:
            await webhook.edit_message(discord_msg_id, content=parsed)
            logger.info(
                f"✏️ Edited Discord (webhook) message id={discord_msg_id} (sneed_id={sneed_id})")
        except Exception as e:
            logger.error(
                f"❌ Failed to edit Discord message id={discord_msg_id}: {e}")

    async def _handle_sneed_delete(self, sneed_id: int):
        try:
            sneed_id = int(sneed_id)
        except Exception:
            return
        discord_msg_id = self.sneed_to_discord.get(sneed_id)
        if not discord_msg_id:
            logger.debug(f"No discord mapping for sneed delete id={sneed_id}")
            return
        if not self.session:
            logger.error("❌ No HTTP session for webhook delete")
            return

        webhook = discord.Webhook.from_url(
            DISCORD_WEBHOOK_URL, session=self.session)
        try:
            await webhook.delete_message(discord_msg_id)
            logger.info(
                f"🗑️ Deleted Discord (webhook) message id={discord_msg_id} (sneed_id={sneed_id})")
            self.sneed_to_discord.pop(sneed_id, None)
            self.discord_to_sneed.pop(discord_msg_id, None)
            self.sneed_usernames.pop(sneed_id, None)
        except Exception as e:
            logger.error(
                f"❌ Failed to delete Discord message id={discord_msg_id}: {e}")

    # -------- Sneedchat connect/disconnect (outage embed) --------
    async def on_sneed_connect(self):
        logger.info("🟢 Sneedchat connected")
        if self.bot.is_ready():
            await self.bot.change_presence(status=discord.Status.online)

        # Get outage stats before finalizing
        stats = self._get_outage_stats()

        # finalize outage embed if present
        if self.outage_message:
            try:
                elapsed = int(time.time() - (self.outage_start or time.time()))
                attempts = getattr(self.sneed_client, "reconnect_attempts", 0)

                # Build embed based on whether system is unstable
                if stats["is_unstable"]:
                    embed = discord.Embed(
                        title="🌉 Bridge Status",
                        description="✅ **Sneedchat reconnected (instability resolved)**",
                        color=0x00FF00)
                    embed.add_field(
                        name="Last Incident Duration",
                        value=f"{elapsed}s",
                        inline=True)
                    embed.add_field(name="Total Downtime (10min)",
                                    value=f"{int(stats['total_downtime'])}s",
                                    inline=True)
                    embed.add_field(
                        name="Outages (10min)", value=str(
                            stats["count"]), inline=True)
                else:
                    embed = discord.Embed(
                        title="🌉 Bridge Status",
                        description="✅ **Sneedchat reconnected**",
                        color=0x00FF00
                    )
                    embed.add_field(
                        name="Downtime",
                        value=f"{elapsed}s",
                        inline=True)
                    embed.add_field(
                        name="Reconnect Attempts",
                        value=str(attempts),
                        inline=True)

                embed.add_field(
                    name="Room ID", value=str(
                        self.sneed_client.room_id), inline=True)

                try:
                    if isinstance(self.outage_message, discord.Message):
                        await self.outage_message.edit(content=None, embed=embed)
                    else:
                        # attempt webhook edit if outage_message is webhook
                        # response
                        webhook = discord.Webhook.from_url(
                            DISCORD_WEBHOOK_URL, session=self.session)
                        await webhook.edit_message(getattr(self.outage_message, "id", self.outage_message), embed=embed)
                    logger.info("📝 Outage notice updated as restored")
                except Exception as e:
                    logger.error(
                        f"Failed to update outage message on reconnect: {e}")
            except Exception as e:
                logger.error(f"Error finalizing outage message: {e}")

            # Schedule deletion 2 minutes after reconnect
            await self._schedule_outage_cleanup()
        else:
            # No outage message, but still schedule cleanup (cleanup after 2
            # min if Sneedchat goes down again and comes back)
            pass

        # After reconnect, try flushing queued_outbound
        asyncio.create_task(self._flush_queued_messages())

    async def on_sneed_disconnect(self):
        logger.warning("🔴 Sneedchat disconnected")
        if self.bot.is_ready():
            await self.bot.change_presence(status=discord.Status.idle)

        # Record this outage event
        self.outage_events.append(time.time())

        # Clean up old events outside the 10-minute window
        now = time.time()
        self.outage_events = [
            ts for ts in self.outage_events if now -
            ts <= OUTAGE_INSTABILITY_WINDOW]

        # If there's an existing outage message, delete old ones and reset
        if self.outage_message:
            logger.debug("Deleting old outage message due to new outage")
            try:
                if isinstance(self.outage_message, discord.Message):
                    await self.outage_message.delete()
                else:
                    try:
                        webhook = discord.Webhook.from_url(
                            DISCORD_WEBHOOK_URL, session=self.session)
                        await webhook.delete_message(getattr(self.outage_message, "id", self.outage_message))
                    except Exception:
                        pass
            except Exception:
                pass

            self.outage_message = None
            self.outage_start = None

            # Cancel cleanup task if running
            if self.outage_cleanup_task and not self.outage_cleanup_task.done():
                self.outage_cleanup_task.cancel()
                try:
                    await self.outage_cleanup_task
                except asyncio.CancelledError:
                    pass

            # Cancel updater task if running
            if self.outage_task and not self.outage_task.done():
                self.outage_task.cancel()
                try:
                    await self.outage_task
                except asyncio.CancelledError:
                    pass

        # Get current stats
        stats = self._get_outage_stats()

        # record outage start and post embed
        self.outage_start = time.time()
        current_attempts = getattr(self.sneed_client, "reconnect_attempts", 0)
        try:
            channel = self.bot.get_channel(DISCORD_CHANNEL_ID)

            # Build embed based on stability
            if stats["is_unstable"]:
                embed = discord.Embed(
                    title="🌉 Bridge Status",
                    description="⚠️ **Sneedchat unstable - multiple reconnections**",
                    color=0xFF0000)
                embed.add_field(
                    name="Outages (10min)", value=str(
                        stats["count"]), inline=True)
                embed.add_field(
                    name="Last Outage Duration",
                    value="0s",
                    inline=True)
                embed.add_field(name="Total Downtime",
                                value=f"{int(stats['total_downtime'])}s",
                                inline=True)
            else:
                embed = discord.Embed(
                    title="🌉 Bridge Status",
                    description="⚠️ **Sneedchat disconnected**",
                    color=0xFF0000
                )
                embed.add_field(
                    name="Outage Duration",
                    value="0s",
                    inline=True)
                embed.add_field(
                    name="Reconnect Attempts",
                    value=str(current_attempts),
                    inline=True)

            embed.add_field(
                name="Room ID",
                value=str(
                    self.sneed_client.room_id),
                inline=True)

            if channel:
                self.outage_message = await channel.send(embed=embed)
                logger.info("📝 Outage notice posted to Discord")
            else:
                # fallback to webhook if channel isn't available
                if self.session:
                    webhook = discord.Webhook.from_url(
                        DISCORD_WEBHOOK_URL, session=self.session)
                    sent = await webhook.send(embed=embed, username="SneedBridge", wait=True)
                    logger.info(
                        "📝 Outage notice posted to Discord via webhook")
                    self.outage_message = sent
                else:
                    logger.error(
                        "No channel found and no session available to post outage notice")

            # start updater task
            async def updater():
                try:
                    while self.outage_message and not self.sneed_client.connected:
                        elapsed = int(time.time() -
                                      (self.outage_start or time.time()))
                        attempts = getattr(
                            self.sneed_client, "reconnect_attempts", 0)
                        current_stats = self._get_outage_stats()

                        # Update embed based on stability
                        if current_stats["is_unstable"]:
                            embed = discord.Embed(
                                title="🌉 Bridge Status",
                                description="⚠️ **Sneedchat outage ongoing (system unstable)**",
                                color=0xFF0000)
                            embed.add_field(
                                name="Outages (10min)", value=str(
                                    current_stats["count"]), inline=True)
                            embed.add_field(
                                name="Last Outage Duration", value=f"{elapsed}s", inline=True)
                            embed.add_field(
                                name="Total Downtime", value=f"{int(current_stats['total_downtime'])}s", inline=True)
                        else:
                            embed = discord.Embed(
                                title="🌉 Bridge Status",
                                description="⚠️ **Sneedchat outage ongoing**",
                                color=0xFF0000
                            )
                            embed.add_field(
                                name="Outage Duration", value=f"{elapsed}s", inline=True)
                            embed.add_field(
                                name="Reconnect Attempts", value=str(attempts), inline=True)

                        embed.add_field(
                            name="Room ID", value=str(
                                self.sneed_client.room_id), inline=True)

                        try:
                            if isinstance(
                                    self.outage_message, discord.Message):
                                await self.outage_message.edit(embed=embed)
                            else:
                                try:
                                    webhook = discord.Webhook.from_url(
                                        DISCORD_WEBHOOK_URL, session=self.session)
                                    await webhook.edit_message(getattr(self.outage_message, "id", self.outage_message), embed=embed)
                                except Exception:
                                    logger.debug(
                                        "Could not edit outage webhook message; skipping edit")
                        except Exception as e:
                            logger.error(
                                f"Failed to update outage message: {e}")
                        await asyncio.sleep(OUTAGE_UPDATE_INTERVAL)
                except asyncio.CancelledError:
                    logger.debug("Outage updater task cancelled")
                    return

            self.outage_task = asyncio.create_task(updater())
        except Exception as e:
            logger.error(f"Failed to send outage notice: {e}")

    # -------- Queue flush & maintenance --------
    async def _flush_queued_messages(self):
        """Attempt to send queued messages to Sneedchat after reconnection."""
        if not self.queued_outbound:
            return
        logger.info(
            f"Flushing {len(self.queued_outbound)} queued messages to Sneedchat")
        now = time.time()
        # iterate copy to allow removal
        for entry in list(self.queued_outbound):
            age = now - entry.get("ts", now)
            channel_id = entry.get("channel_id")
            channel = self.bot.get_channel(channel_id)
            if age > QUEUED_MESSAGE_TTL:
                # abandon and inform channel
                try:
                    if channel:
                        await channel.send(f"❌ Failed to deliver message queued {int(age)}s ago (expired):\n{entry.get('content')[:400]}")
                except Exception:
                    pass
                self.queued_outbound.remove(entry)
                continue
            # try sending
            sent = await self.sneed_client.send_message(entry.get("content"))
            if sent:
                # add to recent_outbound for mapping via echo
                self.recent_outbound.append({
                    "discord_id": entry.get("discord_id"),
                    "content": entry.get("content"),
                    "ts": time.time(),
                    "mapped": False
                })
                # remove from queue
                self.queued_outbound.remove(entry)
                if channel:
                    try:
                        await channel.send("✅ Queued message delivered to Sneedchat after reconnect.")
                    except Exception:
                        pass
            else:
                # still not connected (shouldn't happen inside
                # on_sneed_connect), break
                logger.debug(
                    "Sneedchat still not accepting messages during flush")
                break

    # -------- Cleanup --------
    async def cleanup(self):
        self.shutdown_event.set()

        if self.cleanup_task and not self.cleanup_task.done():
            self.cleanup_task.cancel()
            try:
                await self.cleanup_task
            except asyncio.CancelledError:
                pass

        if self.outage_task and not self.outage_task.done():
            self.outage_task.cancel()
            try:
                await self.outage_task
            except asyncio.CancelledError:
                pass

        if self.outage_cleanup_task and not self.outage_cleanup_task.done():
            self.outage_cleanup_task.cancel()
            try:
                await self.outage_cleanup_task
            except asyncio.CancelledError:
                pass

        if self.session and not self.session.closed:
            await self.session.close()

    async def start(self):
        await self.bot.start(DISCORD_BOT_TOKEN)

# -------- Main --------


async def main():
    logger.info("Starting Discord-Sneedchat Bridge")

    # start cookie refresh
    cookie_service = CookieRefreshService(
        username=BRIDGE_USERNAME, password=BRIDGE_PASSWORD)
    await cookie_service.start()
    logger.info("⏳ Waiting for initial cookie...")
    await cookie_service.wait_for_cookie()
    initial_cookie = cookie_service.get_current_cookie()
    if not initial_cookie:
        logger.error("❌ Failed to obtain initial cookie, cannot start bridge")
        await cookie_service.stop()
        return

    # instantiate sneed client & bridge
    sneed_client = SneedChatClient(
        cookie=initial_cookie,
        room_id=SNEEDCHAT_ROOM_ID,
        reconnect_interval=RECONNECT_INTERVAL,
        cookie_service=cookie_service)
    bridge = DiscordBridge(sneed_client=sneed_client)

    # run the bridge (discord bot)
    try:
        await bridge.start()
    except KeyboardInterrupt:
        logger.info("Shutdown requested")
    finally:
        await cookie_service.stop()
        await sneed_client.disconnect()
        await bridge.cleanup()


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        logger.info("Interrupted by user")
    except Exception as e:
        logger.error(f"Fatal error: {e}")
        exit(1)