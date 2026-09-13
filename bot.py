"""
╔══════════════════════════════════════════════════════════╗
║           Cz Chat Manager — Bot v4.0 Ultra              ║
║  Clean Architecture • Ultra Time Parser • Smart Mod     ║
║  Anti-Spam • Rate Limit • Birthday • DB Optimized       ║
╚══════════════════════════════════════════════════════════╝
"""

from __future__ import annotations

import asyncio
import hashlib
import logging
import os
import re
import time
from collections import defaultdict, deque, OrderedDict
from datetime import datetime, timedelta, timezone
from typing import Optional

import asyncpg
from aiohttp import web
from aiogram import Bot, Dispatcher, F, Router
from aiogram.enums import ChatMemberStatus, ParseMode
from aiogram.exceptions import TelegramBadRequest, TelegramForbiddenError
from aiogram.filters import Command
from aiogram.types import (
    CallbackQuery,
    ChatPermissions,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Message,
)

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)-8s | %(name)s | %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger("CzBot")

BOT_TOKEN: str = os.environ.get(
    "BOT_TOKEN",
    "11111",
)

DATABASE_URL: str = os.environ.get(
    "DATABASE_URL",
    "postgres://avnadmin:A1111111"
    "p111111111unestefan-17be11111111cloud.com:16848/"
    "defaultdb?sslmode=require",
)

SUPER_ADMINS: frozenset[int] = frozenset({8624551006, 8434693684})
BIRTHDAY_CHAT_ID: int = -1002637171253
MAIN_CHAT_ID: int = -1002637171253  # основной рабочий чат (можно менять)
DEAL_CHAT_URL: str = "https://t.me/+E96OibxI2L83ZDAx"
PORT: int = int(os.environ.get("PORT", 16848))
MAX_RATE_LIMIT_SECS: int = 600

DB_LOG_RETENTION_DAYS: int = 90  # 90 дней достаточно для восстановления после рестарта
APPEAL_MAX_LEN: int = 1000

AD_MUTE_FIRST_SECS: int = 86400
AD_MUTE_FIRST_LABEL: str = "1 день"
AD_MUTE_SECOND_SECS: int = 3 * 86400
AD_MUTE_SECOND_LABEL: str = "3 дня"
AD_MUTE_THIRD_SECS: int = 7 * 86400
AD_MUTE_THIRD_LABEL: str = "1 неделю"
APPEAL_HINT: str = "\n🧾 Апелляция: напишите боту в ЛС и нажмите «Подать апелляцию»"

# ── Anti-flood для /start ──────────────────────────────────
_start_flood: dict[int, float] = {}
START_FLOOD_INTERVAL: int = 30

# ── Username самого бота (заполняется при старте) ──────────
TWIN_MIN_LEN: int = 10
BOT_USERNAME: str = ""

# ── Username чата (whitelist — не банить за эти ссылки) ───
# Сюда вносим username нашего чата чтобы не банить за его упоминание
OWN_CHAT_USERNAMES: frozenset[str] = frozenset({
    "chatnft2",       # основной чат
    "czgarant",       # если есть
})


class State:
    pool: Optional[asyncpg.Pool] = None
    garants:  set[int] = set()
    mods:     set[int] = set()
    admins:   set[int] = set()

    twins:   dict[int, set[int]] = defaultdict(set)  # orig_uid → {twin_uids}
    twin_of: dict[int, set[int]] = defaultdict(set)  # twin_uid → {orig_uids}
    twin_allowed: dict[int, set[int]] = defaultdict(set)
    muted_users:  dict[int, set[int]] = defaultdict(set)
    banned_users: dict[int, set[int]] = defaultdict(set)
    # Метаданные мутов/банов: chat_id → {uid → {reason, ts, mod_id}}
    # Без доп. запросов к БД — заполняется при мьюте/бане и при старте
    mute_meta:  dict[int, dict[int, dict]] = defaultdict(dict)
    ban_meta:   dict[int, dict[int, dict]] = defaultdict(dict)
    rate_intervals: dict[int, int] = {}
    rate_last:      dict[int, float] = {}
    warn_cache:     dict[int, dict[int, int]] = defaultdict(dict)
    accepted_deals:   dict[str, int] = {}
    deal_participants: dict[str, str] = {}
    garant_pending_deal: dict[int, str] = {}
    deal_links: dict[str, str] = {}
    deal_status: dict[str, str] = {}
    deal_clarification_target: dict[str, int] = {}
    deal_origin_message: dict[str, int] = {}
    deal_uids: dict[str, list[int]] = {}  # uid участников сделки для доставки в ЛС
    recent_punishments: dict[int, list[tuple[int, float, str]]] = defaultdict(list)
    role_name_cache: dict[str, tuple[float, list[int], set[str]]] = {}
    chat_admin_cache: dict[tuple[int, int], tuple[float, bool]] = {}
    # Уведомление уже обработано: notif_id -> имя обработавшего
    action_taken: dict[str, str] = {}
    # Прощённые хэши: (chat_id, user_id, msg_hash) — бот не трогает это сообщение снова
    hash_pardons: set[tuple[int, int, str]] = set()
    # Пользователи, от которых сейчас ожидается текст апелляции (после нажатия кнопки)
    awaiting_appeal: set[int] = set()
    # uid → {rule_num, msg_id} — ждём ввод своего времени для правила
    awaiting_custom_time: dict[int, dict] = {}
    # notif_id -> хэш сообщения, из-за которого сработало авто-действие
    # (в callback_data хэш не влезает — лимит Telegram 64 байта)
    notif_hash: dict[str, str] = {}
    # notif_id -> инфо об авто-мьюте, ожидающем решения админа/модератора
    pending_auto_mutes: dict[str, dict] = {}
    # notif_id -> {chat_id, message_id, uid, msg_hash, notif_msg_ids: [(admin_id, kb_msg_id)]}
    mat_pending: dict[str, dict] = {}
    # (chat_id, uid) -> бот молча удаляет всё матерное без форварда модераторам
    mat_silent_users: set[tuple[int, int]] = set()
    # (chat_id, uid) — иммунитет от авто-бана/мута ТОЛЬКО в этом чате
    # Снимается если модератор явно пишет «бан» снова в том же чате
    local_immune: set[tuple[int, int]] = set()
    # Журнал авто-банов бота (скамеры, спам и т.п.) — последние записи для обзора
    auto_ban_log: list[dict] = []
    # Кэш настроек чата: chat_id -> {setting: bool}
    settings_cache: dict[int, dict[str, bool]] = {}
    # Кэш правил: rule_num -> {description, action, duration, duration_label}
    rules_cache: dict[int, dict] = {}
    # История последних message_id пользователя в чате (для контекста модераторам)
    # chat_id -> uid -> deque(последние 5 id)
    recent_msgs: dict[int, dict[int, "deque[int]"]] = defaultdict(lambda: defaultdict(lambda: deque(maxlen=5)))
    # notif_id -> {chat_id, uid, msg_hash, notif_msg_ids, ts} — авто-мут навсегда
    # за докс/угрозы слива данных, ждёт решения модератора (бан или размут)
    doxx_pending: dict[str, dict] = {}


st = State()

RULE_REASONS: dict[int, str] = {
    1: "Спам",
    2: "Оскорбление админов / владельца",
    3: "Краш-стикеры",
    4: "18+, нацизм, фашизм и т.п.",
    5: "Оскорбление участников",
    6: "Расчлененка",
    7: "Скам",
    8: "Реклама",
    9: "Клевета на админа / владельца",
}

RULES_TEXT = (
    "📜 <b>Правила чата Cz Гарант:</b>\n\n"
    "1️⃣ <b>Спам</b> → 🔇 Мут <b>5 дней</b>\n"
    "2️⃣ <b>Оскорбление админов / владельца</b> → 🔇 Мут <b>1 день</b>\n"
    "3️⃣ <b>Краш-стикеры</b> → 🔇 Мут <b>1 неделю</b>\n"
    "4️⃣ <b>18+, нацизм, фашизм и т.п.</b> → 🔇 Мут <b>1 день</b>\n"
    "5️⃣ <b>Оскорбление участников</b> → 🔇 Мут <b>1 час</b>\n"
    "6️⃣ <b>Расчлененка</b> → 🔇 Мут <b>1 неделю</b>\n"
    "7️⃣ <b>Скам</b> → 🚫 Бан <b>навсегда</b>\n"
    "8️⃣ <b>Реклама</b> → 🔇 Мут <b>1 неделю</b>\n"
    "9️⃣ <b>Клевета на админа / владельца</b> → 🔇 Мут <b>1 день</b>\n\n"
    "🤝 Будьте вежливы и доброжелательны!\n"
    "⚠️ <i>Написал с твинка пока в муте → 🔇 Мут на твинк до снятия администрацией</i>\n\n"
    "🛡 <b>Вызов гаранта</b>\n\n"
    "• <b>Reply</b> на сообщение участника: <code>/адм текст сделки</code>\n"
    "• Укажите предмет сделки и сумму\n"
    "• У <b>обоих</b> участников должен быть <b>запущен бот</b>\n\n"
    "🧾 <b>Апелляция на наказание:</b>\n"
    "Если вы считаете мут/бан ошибочным — напишите боту в ЛС и нажмите кнопку «Подать апелляцию», "
    "затем опишите ситуацию одним сообщением.\n\n"
    "💬 <code>/админы</code> — список администрации"
)

ADMIN_HELP_TEXT = (
    "🛠 <b>Команды администратора</b>\n"
    "<i>(Reply на сообщение нарушителя)</i>\n\n"
    "⚠️ <code>варн [причина]</code> — предупреждение (3 = бан)\n"
    "♻️ <code>сброс</code> — сбросить варны\n"
    "📊 <code>варны</code> — посмотреть варны\n\n"
    "🔇 <code>мут 1ч причина</code> — мут с причиной\n"
    "🔇 <code>мут 5д 8</code> — мут по правилу №8\n"
    "🔇 <code>мут навсегда причина</code> — бессрочный мут\n"
    "🔊 <code>размут</code> / <code>размут @user</code> / <code>размут ID</code>\n\n"
    "🚫 <code>бан</code> — перманентный бан\n"
    "🚫 <code>бан 1д причина</code> — временный бан\n"
    "✅ <code>разбан</code> / <code>разбан @user</code> / <code>разбан ID</code>\n\n"
    "⏱ <b>Rate Limit:</b>\n"
    "<code>лимит 1мин</code> — ограничить (reply, макс 10 мин)\n"
    "<code>снять лимит</code> — снять (reply)\n\n"
    "📢 <b>Объявление:</b>\n"
    "<code>объяв Текст</code> — закреплённое сообщение\n\n"
    "🧹 <code>purge N</code> — удалить N сообщений (reply, макс 100)\n"
    "📋 <code>автодействия</code> — панель авто-мьютов/банов бота\n"
    "🔍 <code>/whois @user</code> — инфо о пользователе\n"
    "📋 <code>/history @user</code> — история нарушений\n"
    "🏆 <code>/топ</code> — топ нарушителей чата\n"
    "👥 <code>/твинк @user</code> — пометить как твинк (reply)\n"
        "🛡 <code>/адм ...</code> — вызвать гаранта для сделки\n\n"
    "📜 <code>правила</code> | 💬 <code>админы</code> | ❓ <code>помощь</code>\n\n"
    "🛡 <b>Роли (только супер-админы):</b>\n"
    "<code>/добавить_гаранта</code> — reply на сообщение\n"
    "<code>/удалить_гаранта @user</code>\n"
    "<code>/добавить_модератора</code> — reply на сообщение\n"
    "<code>/удалить_модератора @user</code>\n"
    "<code>/добавить_администратора</code> — reply на сообщение\n"
    "<code>/удалить_администратора @user</code>\n"
        "⏱ <b>Форматы времени (ультрагибкие):</b>\n"
    "<code>30с 1м 5мин 2ч 1д 1нед 1мес</code>\n"
    "<code>30s 1m 5min 2h 1d 1w 1mo</code>\n"
    "<code>30 секунд, 5 минут, 2 часа, 1 день, 3 недели</code>\n"
    "<code>навсегда / perm / forever</code> — бессрочный мут"
)

ADMIN_START_TEXT = (
    "👑 <b>Cz Chat Manager</b>\n"
    "Ты супер-администратор. Доступны все функции.\n\n"
    "🛡 <b>Роли:</b>\n"
    "@Timmy_Falcon и @mrtley - лучшие)))\n"
    "<code>/добавить_гаранта</code> — reply на сообщение пользователя\n"
    "<code>/добавить_модератора</code> — reply на сообщение пользователя\n"
    "<code>/добавить_администратора</code> — reply на сообщение пользователя\n\n"
    "📋 <code>/админы</code> — состав администрации\n"
    "❓ <code>помощь</code> — все команды\n\n"
    "👇 Добавь бота в чат:"
)

_RE_MAT = re.compile(
    r"х+[уy]+[йиеёяюь]|х+[уy]+[еe]|пизд|еб[ао]|ёб[ао]н?|"
    r"бля[тд]|блядь|с[уy]к[аеи](?!лент)|сучк|пидо?р|залуп|"
    r"мудак|мудил|уёб|съеб|наеб|заеб|поеб|долбо[её]б|"
    # ── Оскорбительные слова / жаргонизмы ──────────────────
    r"гандон\w*|гондон\w*|пидор\w*|пидар\w*|педик\w*|педр\w*|"
    r"педофил\w*|гомик\w*|говн\w*|дерьм\w*|мраз[ьоеиюя]\w*|"
    r"сволоч\w*|скотин\w*|тварь\w*|твар[ьи]\w*|шлюх\w*|"
    r"проститутк\w*|ублюдок\w*|ублюдк\w*|дегенерат\w*|"
    r"придурок\w*|придурк\w*|дебил\w*|идиот\w*|кретин\w*|"
    r"мразот\w*|уёбищ\w*|уебищ\w*",
    re.IGNORECASE | re.UNICODE,
)

# ── Оскорбления родных (мать, отец и т.п.) ────────────────
_RE_FAMILY_INSULT = re.compile(
    r"(?:тво[юяейого]{1,3}|ваш[ауюем]{0,2}|его|её|их)\s+"
    r"(?:мать|маму|мам[ауе]|мамк[ауи]|папу|пап[ауе]|батю|бат[ья]|отца|отчима|мачех[ау]|"
    r"сестру|сестр[ыу]|братан?[ауе]|брата|братву|бабку|бабушку|деда|дедушку|"
    r"т[её]тю|дядю|племянни\w*|жену|мужа|дочь|дочку|сынк?[ауе]?|детей|ребён?ка|"
    r"родителей|семью|родню|родствен\w*|родн\w*|близк\w*)|"
    r"(?:мать|мама|мамк[ауи]|папа|батя|отец|отчим|мачеха|сестра|брат[ауе]?|бабка|бабушка|"
    r"дед|дедушка|т[её]тя|дядя|жена|муж|дочь|сын|родители|семья|родня|"
    r"родствен\w*|родн\w*|близк\w*)\w*"
    r"\s*[-–—]?\s*(?:тво[яю]|ваша)?\s*"
    r"(?:шлюх\w*|бляд\w*|сук[аи]\w*|тварь\w*|проститутк\w*|мраз\w*|"
    r"падаль\w*|сдохл\w*|умр[иё]\w*|уёб\w*|еб[ао]\w*|пизд\w*|"
    r"урод\w*|мудак\w*|дебил\w*|идиот\w*|дур[аеиы][кц]\w*|тупиц\w*|"
    r"туп[ыоа][йяе]\w*|кретин\w*|конч\w*|"
    r"лох\w*|лошар\w*|гнид\w*|выродок\w*|выродк\w*|ушлёпок\w*|ушлёпк\w*|"
    r"чмо\w*|отброс\w*)",
    re.IGNORECASE | re.UNICODE,
)

# ── Прямые оскорбления участников ("ты + слово") ──────────
# Безопасные слова — почти всегда используются только как оскорбление.
# Двузначные слова (скот, овца) ловим ТОЛЬКО с адресным "ты", чтобы не
# срабатывать на нейтральные упоминания (например, разговор о животных).
_RE_DIRECT_INSULT = re.compile(
    r"\b(?:лох\w*|лошар\w*|гнид\w*|выродок|выродк\w*|ушлёпок|ушлёпк\w*|"
    r"чмо\w*|отброс\w*)\b|"
    r"\bты\s+(?:конченый|конченая|такой|такая|прям|реальн\w*|полн\w*)?\s*"
    r"(?:скот(?!ч)\w*|овц\w*)\b",
    re.IGNORECASE | re.UNICODE,
)

# ── Детектор арабского/персидского/урду текста ───────────
_RE_ARABIC = re.compile(r"[\u0600-\u06FF\u0750-\u077F\u08A0-\u08FF\uFB50-\uFDFF\uFE70-\uFEFF]")
ARABIC_MIN_CHARS: int = 3  # минимум символов чтобы сработало

_RE_PROFILE_SPAM = re.compile(
    r"чат\s+в\s+профил[её]|ссылка\s+в\s+профил[её]|канал\s+в\s+профил[её]|группа\s+в\s+профил[её]"
    r"профил[её]\s+есть\s+(?:чат|канал|ссылка|группа)|"
    r"загляни\s+в\s+(?:мой\s+)?профил[ья]|"
    r"смотри\s+в\s+(?:мой\s+)?профил[ья]|"
    r"зайди\s+в\s+(?:мой\s+)?профил[ья]|"
    r"перейди\s+в\s+(?:мой\s+)?профил[ья]|"
    r"в\s+(?:моём?|мем)\s+профил[её]\s+(?:есть\s+)?(?:чат|канал|ссылк|группа)|"
    r"информаци[яи]\s+в\s+профил[её]|"
    r"заходи\s+к\s+нам|залетай|переходи|подпишись|жми\s+на|кликни|"
    r"лучш(?:ий|ая|ее)\s+(?:чат|канал|бот|группа)|топ.{0,5}чат|топ.{0.5}группа",
    re.IGNORECASE | re.UNICODE,
)

# ══════════════════════════════════════════════════════════
# ГЛАВНЫЙ ДЕТЕКТОР ССЫЛОК — максимально широкий охват
# ══════════════════════════════════════════════════════════

# 1. Прямые Telegram-ссылки (все форматы)
_RE_TG_LINKS = re.compile(
    r"""
    (?:https?://)?                          # опциональный протокол
    (?:www\.)?                              # опциональный www
    (?:
        t\.me |                             # основной домен
        telegram\.me |                      # альтернативный домен
        telegram\.dog |                     # редкий алиас
        telegra\.ph                         # Telegraph (статьи)
    )
    /
    (?:
        joinchat/[a-zA-Z0-9_-]+ |          # старые приватные ссылки
        \+[a-zA-Z0-9_-]+ |                 # новые приватные ссылки (+XXXX)
        [a-zA-Z][a-zA-Z0-9_]{0,31}         # публичные username (от 1 символа!)
        (?:/\d+)?                           # опциональный ID сообщения
    )
    """,
    re.IGNORECASE | re.VERBOSE,
)

# 2. tg:// схемы
_RE_TG_SCHEME = re.compile(
    r"tg://(?:join\?invite|resolve\?domain)=[a-zA-Z0-9_@-]+",
    re.IGNORECASE,
)

# 3. @упоминания которые ВЫГЛЯДЯТ как реклама чата/канала
# (только если рядом есть рекламный контекст — проверяем отдельно)
_RE_AT_MENTION = re.compile(r"@([a-zA-Z][a-zA-Z0-9_]{3,})")

# 4. Замаскированные ссылки (пробелы, точки заменены)
_RE_MASKED_TG = re.compile(
    r"""
    (?:
        t[\s\.\,\-_]*\.[\s\.\,\-_]*me |    # t . me / t.me с пробелами
        telegram[\s\.\,\-_]*\.[\s\.\,\-_]*(?:me|org|com|dog)
    )
    [\s\.\,\-_]*/[\s\.\,\-_]*
    [a-zA-Z0-9_\+][a-zA-Z0-9_\+\-]*
    """,
    re.IGNORECASE | re.VERBOSE,
)

# 5. Ссылки на другие мессенджеры/платформы (рекламного характера)
_RE_OTHER_PROMO = re.compile(
    r"""
    (?:https?://)?(?:www\.)?
    (?:
        discord\.(?:gg|com/invite) |        # Discord
        vk\.com/(?:club|public|im) |        # ВКонтакте группы
        chat\.whatsapp\.com |               # WhatsApp
        invite\.viber\.com |                # Viber
        signal\.group |                     # Signal
        matrix\.to                          # Matrix
    )
    /[a-zA-Z0-9_\-\+/]+
    """,
    re.IGNORECASE | re.VERBOSE,
)

# ══════════════════════════════════════════════════════════
# Контекстные слова рекламы (@username + контекст = реклама)
# ══════════════════════════════════════════════════════════
_AD_CONTEXT_WORDS = re.compile(
    r"подпис|вступ|заход|залет|перейд|жми|кликн|канал|чат|группа|"
    r"паблик|сообщество|subscribe|join|channel|follow|check\s*out",
    re.IGNORECASE | re.UNICODE,
)

# ══════════════════════════════════════════════════════════
# ДЕТЕКТОР ЭСКОРТА / 18+ КОНТЕНТА (Правило 4)
# ══════════════════════════════════════════════════════════

# Паттерн 1: объявление о продаже/показе себя за деньги
_RE_ESCORT_SELL = re.compile(
    r"""
    (?:
        (?:за\s*\d+\s*(?:руб|р\b|₽|рублей?|$)) |   # "за 100 руб" / "за 100₽"
        (?:показ(?:ываю|ать|ую)\s+себя) |             # "показываю себя"
        (?:показ(?:ываю|ать|ую)\s+(?:фото|видео|кружк|себя)) |
        (?:продаю?\s+(?:фото|видео|контент|доступ)) |
        (?:платн(?:ый|ые|ое|о)\s+контент)
    )
    """,
    re.IGNORECASE | re.VERBOSE | re.UNICODE,
)

# Паттерн 2: предложение интимного контента (фото/видео/звонки)
_RE_ESCORT_CONTENT = re.compile(
    r"""
    (?:
        (?:видео|фото|кружоч?к(?:и)?|звоноч?к(?:и)?|войс(?:ы)?)
        .{0,30}
        (?:за\s*\d+|платн|продаю?|заказ(?:ать|ывай)?|пиши(?:те)?(?:\s+мальчики?)?)
    ) |
    (?:
        (?:за\s*\d+\s*(?:руб|р\b|₽|рублей?)?)
        .{0,30}
        (?:видео|фото|кружоч?к(?:и)?|звоноч?к(?:и)?)
    )
    """,
    re.IGNORECASE | re.VERBOSE | re.UNICODE,
)

# Паттерн 3: предложение обмена интимным контентом
_RE_ESCORT_INTIM = re.compile(
    r"""
    (?:
        (?:обменя(?:ть)?ся|обмен)\s+(?:интимк|фото|видео|ню|контентом) |
        (?:интимк(?:ами|и)?)\s+(?:бесплатно|обмен|меняюсь|скину|кидаю) |
        (?:скину|кидаю|кину)\s+(?:первой?|первым|первая|свои?)\b(?!.*гарант) |
        (?:ищу\s+(?:с\s+кем|кого).{0,40}(?:интимк|фото|видео|ню|обнаж))
    )
    """,
    re.IGNORECASE | re.VERBOSE | re.UNICODE,
)

# Паттерн 4: реклама эскорт-аккаунтов (формат объявления знакомств + контент)
_RE_ESCORT_AD = re.compile(
    r"""
    (?:
        (?:пишите?\s+(?:мальчики?|парни?|мужчины?|всем)) |
        (?:реальность\s+докажу?) |
        (?:докажу?\s+реальность) |
        (?:кидаю\s+первой?) |
        (?:бесплатно\s+пиши(?:\s+в\s+лс)?) |
        (?:пиши\s+в\s+лс\b)
    )
    .{0,80}
    (?:фото|видео|кружк|звонок|контент|интимк|показ)
    |
    (?:фото|видео|кружк|звонок|контент|интимк|показ)
    .{0,80}
    (?:
        (?:пишите?\s+(?:мальчики?|парни?|мужчины?)) |
        (?:реальность\s+докажу?) |
        (?:кидаю\s+первой?) |
        (?:бесплатно\s+пиши)
    )
    """,
    re.IGNORECASE | re.VERBOSE | re.UNICODE,
)


def has_escort_content(text: str) -> tuple[bool, str]:
    """Проверяет наличие эскорт/18+ объявлений. Возвращает (найдено, причина)."""
    if not text:
        return False, ""
    if _RE_ESCORT_SELL.search(text) and _RE_ESCORT_CONTENT.search(text):
        return True, "Эскорт/18+ контент (продажа)"
    if _RE_ESCORT_INTIM.search(text):
        return True, "Эскорт/18+ контент (обмен интимом)"
    if _RE_ESCORT_AD.search(text):
        return True, "Эскорт/18+ объявление"
    return False, ""


# ══════════════════════════════════════════════════════════
# ДЕТЕКТОР АЗАРТНЫХ ИГР (Правило 1.2 со страницы правил)
# «Зазывать в азартные игры» → мут 24ч
# ══════════════════════════════════════════════════════════
_RE_GAMBLING_BRAND = re.compile(
    r"1x\s*bet|мелбет|melbet|фонбет|fonbet|вавада|vavada|пин[\s-]?ап|pin[\s-]?up|"
    r"риобет|riobet|париматч|parimatch|леон\s*бет|leon\s*bet|олимпбет|olimpbet|"
    r"betwinner|бетвиннер|1win|1вин|винлайн|winline|марафон\s*бет|melbet",
    re.IGNORECASE | re.UNICODE,
)
_RE_GAMBLING_GENERIC = re.compile(
    r"казино|букмекер\w*|ставки\s+на\s+спорт|фрибет|"
    r"игровы[ех]\s+автомат\w*|слот[ыа]\b|рулетк[ауи]|джекпот|"
    r"промокод.{0,20}(?:казино|ставк\w*|депозит|фрибет)|"
    r"депозит.{0,20}(?:казино|ставк\w*)",
    re.IGNORECASE | re.UNICODE,
)


def has_gambling_content(text: str) -> bool:
    if not text:
        return False
    return bool(_RE_GAMBLING_BRAND.search(text) or _RE_GAMBLING_GENERIC.search(text))


# ══════════════════════════════════════════════════════════
# ДЕТЕКТОР ПОПРОШАЙНИЧЕСТВА (Правило 1.7 со страницы правил)
# «Попрошайничество в любом его виде» → мут 24ч
# Намеренно НЕ ловит обычные обсуждения сумм по сделкам/займам —
# только явные формулировки прошения/сбора денег без встречной услуги.
# ══════════════════════════════════════════════════════════
_RE_BEGGING = re.compile(
    r"скинь(?:те)?\s+кто\s+сколько\s+может|"
    r"закинь(?:те)?.{0,15}(?:просто\s+так|без\s?возмездно)|"
    r"нет\s+денег\s+на\s+(?:еду|лекарств\w*|лечение)|"
    r"не\s+хватает\s+на\s+(?:еду|лекарств\w*|лечение)|"
    r"сбор\s+средств(?:\s+на)?|сбор\s+на\s+лечение|"
    r"помогите\s+материально|пожертвуйте|нечего\s+есть|"
    r"подайте\s+(?:кто\s+)?сколько\s+(?:можете|сможете)",
    re.IGNORECASE | re.UNICODE,
)


def has_begging_content(text: str) -> bool:
    if not text:
        return False
    return bool(_RE_BEGGING.search(text))


# ══════════════════════════════════════════════════════════
# ДЕТЕКТОР УГРОЗ ДОКСОМ/СВАТОМ/СЛИВОМ ДАННЫХ
# (раздел «Запрещено» + 3.3 со страницы правил — категория без апелляции)
# Ловит только явные УГРОЗЫ (намерение слить/пробить/сдать), а не сам
# факт публикации чужих данных — это бот достоверно отличить не может
# и оставлено на ручную модерацию через reply-команды.
# ══════════════════════════════════════════════════════════
_RE_DOXX_THREAT = re.compile(
    r"слив\w*\s+(?:твои[хм]?|ваши[хм]?|его|её|их|личны[ех])\s*(?:данны[ех]|информаци\w*|адрес\w*)|"
    r"(?:солью|сольём|сольёшь|сольёте|сольёт|сольют|слил[аи]?)"
    r"\s+(?:твои?|ваши?|его|её|их|личны[ех])\s*(?:данны[ех]|информаци\w*|адрес\w*)|"
    r"пробь?(?:ю|ём|ешь)\s+по\s+баз\w*|пробив\s+по\s+(?:номеру|базе|базам)|"
    r"узна[юем]\s+(?:твой|ваш)\s+адрес|найд[уеё]м?\s+тебя|тебя\s+найд[уеё]м?|"
    r"сдам\s+(?:тебя\s+)?(?:в\s+полицию|ментам|органам)|"
    r"снес[уёем]+\s+(?:твой|ваш)\s+аккаунт|доксн(?:у|ём|ешь|уть)|"
    r"сватн(?:у|ём|ешь|уть)\s+тебя|разошл[юём]\s+(?:твои?|ваши?)\s+данны[ех]",
    re.IGNORECASE | re.UNICODE,
)


def has_doxx_threat(text: str) -> bool:
    if not text:
        return False
    return bool(_RE_DOXX_THREAT.search(text))


# ══════════════════════════════════════════════════════════
# ДЕТЕКТОР СОМНИТЕЛЬНЫХ УСЛУГ (2.3 со страницы правил)
# Расширение анти-рекламы: не сама ссылка, а предложение теневых услуг
# ══════════════════════════════════════════════════════════
_RE_SUSPICIOUS_SERVICE = re.compile(
    r"взлом\s+аккаунт\w*|услуги\s+хакера|хакерские\s+услуги|"
    r"пробив\s+по\s+баз[аеы]м?(?:\s+данных)?|"
    r"снятие\s+(?:бана|ограничени\w*)\s+(?:за\s+деньги|платно)|"
    r"обнал(?:ичк\w*|ичу|ичим|ич)",
    re.IGNORECASE | re.UNICODE,
)


def has_suspicious_service(text: str) -> bool:
    if not text:
        return False
    return bool(_RE_SUSPICIOUS_SERVICE.search(text))


_TIME_UNITS: list[tuple[re.Pattern, int]] = [
    (re.compile(r"месяц(?:ев|а)?|мес(?:яц)?|mo(?:nth)?s?", re.I | re.U), 2592000),
    (re.compile(r"недел[юьяи]|неделя|нед|w(?:eek)?s?", re.I | re.U), 604800),
    (re.compile(r"дн[ейяю]|день|дней|дня|дн|д(?=[^а-яё]|$)|d(?:ay)?s?", re.I | re.U), 86400),
    (re.compile(r"час(?:ов|а)?|ч(?=[^а-яё]|$)|h(?:(?:ou)?r)?s?", re.I | re.U), 3600),
    (re.compile(r"минут[аеу]?|мин(?:уту|уты|уте|ута)?|м(?=[^а-яё]|$)|min(?:ute)?s?", re.I | re.U), 60),
    (re.compile(r"секунд[аеу]?|сек(?:унда|унды|унде)?|с(?=[^а-яё]|$)|s(?:ec(?:ond)?)?s?", re.I | re.U), 1),
]

# Маркеры "навсегда" для мута/бана
_RE_FOREVER = re.compile(
    r"(?:\b(?:навсегда|перм|permanent|forever|perm|infinity|inf)\b|∞)",
    re.IGNORECASE | re.UNICODE,
)

_RE_TIME_FULL = re.compile(
    r"(\d+)\s*"
    r"(месяц(?:ев|а)?|мес(?:яц)?|mo(?:nth)?s?|"
    r"недел[юьяи]?|неделя?|нед|w(?:eek)?s?|"
    r"дн[ейяю]?|день|дней|дня|дн|д(?=[^а-яё\d]|$)|d(?:ay)?s?|"
    r"час(?:ов|а)?|ч(?=[^а-яё\d]|$)|h(?:(?:ou)?r)?s?|"
    r"минут[аеу]?|мин(?:уту|уты|уте|ута)?|м(?=[^а-яё\d]|$)|min(?:ute)?s?|"
    r"секунд[аеу]?|сек(?:унда|унды|унде)?|с(?=[^а-яё\d]|$)|s(?:ec(?:ond)?)?s?)",
    re.IGNORECASE | re.UNICODE,
)

_RE_MENTION = re.compile(r"@[a-zA-Z0-9_]{4,}")
_DEAL_WORDS = frozenset(["сделк", "купить", "продать", "обмен", "хочу", "предлага"])


_DEAL_REQUEST_RE = re.compile(
    r"""
    ^\s*
    (?P<author>@[a-zA-Z0-9_]{4,})
    \s+
    (?P<intent>
        хочу\s+провести\s+сделку |
        хочу\s+сделку |
        нужен\s+гарант |
        вызываю\s+гаранта |
        сделка
    )
    \s+
    (?:с\s+)?
    (?P<partner>@[a-zA-Z0-9_]{4,})
    (?P<rest>.*)
    $
    """,
    re.IGNORECASE | re.VERBOSE | re.UNICODE,
)

_DEAL_SUBJECT_HINTS = re.compile(
    r"купить|продать|обменять|обмен|товар|услуг|аккаунт|канал|звез|нфт|nft|usdt|руб|₽|доллар|paypal|telegram",
    re.IGNORECASE | re.UNICODE,
)


def detect_deal_role(details: str) -> tuple[str, str]:
    text = (details or "").lower()
    if any(x in text for x in ["хочу купить", "куплю", "покупаю", "ищу купить"]):
        return "buyer", "Покупка"
    if any(x in text for x in ["продаю", "хочу продать", "продам"]):
        return "seller", "Продажа"
    if any(x in text for x in ["обмен", "обменяю", "меняю"]):
        return "exchange", "Обмен"
    return "unknown", "Сделка"


def extract_deal_amount(details: str) -> str:
    text = details or ""
    patterns = [
        r"(\d+[\d\s]{0,12})\s*(₽|руб(?:лей|ля|.)?|rur|rub)",
        r"(\d+[\d\s]{0,12})\s*(usdt|usd|\$)",
        r"(\d+[\d\s]{0,12})\s*(ton|stars|зв[её]зд)",
    ]
    for pat in patterns:
        m = re.search(pat, text, re.I)
        if m:
            return f"{m.group(1).strip()} {m.group(2)}"
    return "не указана"


_FOREVER_SECS = -1  # Сигнальное значение для "навсегда" (мут без until_date)


def parse_time(text: str) -> tuple[Optional[int], Optional[str]]:
    """Парсит время из строки.
    Возвращает (секунды, метка) или (None, None) если не распознано.
    Для «навсегда» возвращает (0, 'навсегда') — мут без срока.
    """
    if not text:
        return None, None
    text = text.strip()

    # Сначала проверяем «навсегда» — до числового парсинга
    if _RE_FOREVER.search(text):
        return _FOREVER_SECS, "навсегда"  # -1 = бессрочно

    total = 0
    found = False
    for match in _RE_TIME_FULL.finditer(text):
        val      = int(match.group(1))
        unit_str = match.group(2).lower()
        for pattern, multiplier in _TIME_UNITS:
            if pattern.search(unit_str):
                total += val * multiplier
                found  = True
                break
    if not found or total <= 0:
        return None, None
    return total, _fmt_duration(total)


def _fmt_duration(secs: int) -> str:
    if secs >= 2592000:
        v = secs // 2592000
        return f"{v} {'месяц' if v == 1 else 'месяца' if 2 <= v <= 4 else 'месяцев'}"
    if secs >= 604800:
        v = secs // 604800
        return f"{v} {'неделю' if v == 1 else 'недели' if 2 <= v <= 4 else 'недель'}"
    if secs >= 86400:
        v = secs // 86400
        return f"{v} {'день' if v == 1 else 'дня' if 2 <= v <= 4 else 'дней'}"
    if secs >= 3600:
        v = secs // 3600
        return f"{v} {'час' if v == 1 else 'часа' if 2 <= v <= 4 else 'часов'}"
    if secs >= 60:
        v = secs // 60
        return f"{v} {'минуту' if v == 1 else 'минуты' if 2 <= v <= 4 else 'минут'}"
    return f"{secs} {'секунду' if secs == 1 else 'секунды' if 2 <= secs <= 4 else 'секунд'}"


_INIT_SQL = """
CREATE TABLE IF NOT EXISTS warnings (
    user_id   BIGINT,
    chat_id   BIGINT,
    warns     INTEGER DEFAULT 0,
    last_warn TIMESTAMPTZ,
    reason    TEXT DEFAULT '',
    PRIMARY KEY (user_id, chat_id)
);
CREATE TABLE IF NOT EXISTS warn_history (
    id           SERIAL PRIMARY KEY,
    user_id      BIGINT,
    chat_id      BIGINT,
    warn_number  INTEGER,
    reason       TEXT,
    moderator_id BIGINT,
    ts           TIMESTAMPTZ DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS action_logs (
    id           SERIAL PRIMARY KEY,
    action       TEXT,
    moderator_id BIGINT,
    target_id    BIGINT,
    chat_id      BIGINT,
    reason       TEXT,
    ts           TIMESTAMPTZ DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS garant_admins (
    user_id  BIGINT PRIMARY KEY,
    username TEXT,
    added_by BIGINT,
    added_at TIMESTAMPTZ DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS moderators (
    user_id  BIGINT PRIMARY KEY,
    username TEXT,
    added_by BIGINT,
    added_at TIMESTAMPTZ DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS administrators (
    user_id  BIGINT PRIMARY KEY,
    username TEXT,
    added_by BIGINT,
    added_at TIMESTAMPTZ DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS chat_settings (
    chat_id         BIGINT PRIMARY KEY,
    welcome_message TEXT,
    antilink        BOOLEAN DEFAULT TRUE,
    antimat         BOOLEAN DEFAULT TRUE,
    antiescort      BOOLEAN DEFAULT TRUE,
    antiarabic      BOOLEAN DEFAULT TRUE,
    antifiles       BOOLEAN DEFAULT TRUE,
    antitwin        BOOLEAN DEFAULT TRUE,
    antiprofilespam BOOLEAN DEFAULT TRUE,
    antigambling    BOOLEAN DEFAULT TRUE,
    antibegging     BOOLEAN DEFAULT TRUE,
    antidoxx        BOOLEAN DEFAULT TRUE,
    antisuspicious  BOOLEAN DEFAULT TRUE
);
CREATE TABLE IF NOT EXISTS user_notes (
    id       SERIAL PRIMARY KEY,
    user_id  BIGINT,
    chat_id  BIGINT,
    note     TEXT,
    added_by BIGINT,
    added_at TIMESTAMPTZ DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS twin_accounts (
    id          SERIAL PRIMARY KEY,
    user_id     BIGINT,
    twin_of     BIGINT,
    chat_id     BIGINT,
    added_by    BIGINT,
    added_at    TIMESTAMPTZ DEFAULT NOW(),
    UNIQUE(user_id, twin_of, chat_id)
);
CREATE TABLE IF NOT EXISTS appeals (
    id          SERIAL PRIMARY KEY,
    user_id     BIGINT,
    username    TEXT,
    text        TEXT,
    status      TEXT DEFAULT 'open',
    resolved_by BIGINT,
    created_at  TIMESTAMPTZ DEFAULT NOW(),
    resolved_at TIMESTAMPTZ
);
CREATE TABLE IF NOT EXISTS automod_state (
    user_id BIGINT,
    chat_id BIGINT,
    ad_hits INTEGER DEFAULT 0,
    last_ad TIMESTAMPTZ DEFAULT NOW(),
    PRIMARY KEY (user_id, chat_id)
);
CREATE TABLE IF NOT EXISTS rules (
    rule_num    INTEGER PRIMARY KEY,
    description TEXT    NOT NULL,
    action      TEXT    NOT NULL DEFAULT 'mute',
    duration    INTEGER DEFAULT 0,
    duration_label TEXT DEFAULT ''
);
CREATE TABLE IF NOT EXISTS twin_allowlist (
    user_id BIGINT,
    chat_id BIGINT,
    allowed_by BIGINT,
    added_at TIMESTAMPTZ DEFAULT NOW(),
    PRIMARY KEY (user_id, chat_id)
);
"""


async def db_init() -> None:
    st.pool = await asyncpg.create_pool(
        DATABASE_URL, min_size=1, max_size=5,
        command_timeout=10,
    )
    async with st.pool.acquire() as c:
        await c.execute(_INIT_SQL)
        _setting_cols = [
            ("antilink",        "TRUE"),
            ("antimat",         "TRUE"),
            ("antiescort",      "TRUE"),
            ("antiarabic",      "TRUE"),
            ("antifiles",       "TRUE"),
            ("antitwin",        "TRUE"),
            ("antiprofilespam", "TRUE"),
            ("antigambling",    "TRUE"),
            ("antibegging",     "TRUE"),
            ("antidoxx",        "TRUE"),
            ("antisuspicious",  "TRUE"),
        ]
        for col, default in _setting_cols:
            await c.execute(
                f"ALTER TABLE chat_settings ADD COLUMN IF NOT EXISTS {col} BOOLEAN DEFAULT {default}"
            )
    # Заполняем таблицу правил дефолтами если она пуста
    async with st.pool.acquire() as c:
        count = await c.fetchval("SELECT COUNT(*) FROM rules")
        if count == 0:
            _DEFAULT_RULES = [
                (1, "Спам",                          "mute",   5*86400,   "5 дней"),
                (2, "Оскорбление админов / владельца","mute",  86400,     "1 день"),
                (3, "Краш-стикеры",                  "mute",   7*86400,   "1 неделю"),
                (4, "18+, нацизм, фашизм и т.п.",    "mute",   86400,     "1 день"),
                (5, "Оскорбление участников",         "mute",   3600,      "1 час"),
                (6, "Расчлененка",                   "mute",   7*86400,   "1 неделю"),
                (7, "Скам",                          "ban",    0,         "навсегда"),
                (8, "Реклама",                       "mute",   7*86400,   "1 неделю"),
                (9, "Клевета на админа / владельца", "mute",   86400,     "1 день"),
            ]
            await c.executemany(
                "INSERT INTO rules (rule_num, description, action, duration, duration_label) "
                "VALUES ($1,$2,$3,$4,$5) ON CONFLICT DO NOTHING",
                _DEFAULT_RULES,
            )
        rows = await c.fetch("SELECT * FROM rules ORDER BY rule_num")
    st.rules_cache = {r["rule_num"]: dict(r) for r in rows}

    async with st.pool.acquire() as c:
        for row in await c.fetch("SELECT user_id FROM garant_admins"):
            st.garants.add(row["user_id"])
        for row in await c.fetch("SELECT user_id FROM moderators"):
            st.mods.add(row["user_id"])
        for row in await c.fetch("SELECT user_id FROM administrators"):
            st.admins.add(row["user_id"])

        for row in await c.fetch("SELECT user_id, twin_of FROM twin_accounts"):
            # user_id — твинк; twin_of — оригинал
            # st.twins[orig] → набор твинков (для find_recent_related_punishment)
            st.twins[row["twin_of"]].add(row["user_id"])
            # st.twin_of[twin] → набор оригиналов (направленная связь — только твинки попадают под санкции)
            st.twin_of[row["user_id"]].add(row["twin_of"])
        for row in await c.fetch("SELECT user_id, chat_id FROM twin_allowlist"):
            st.twin_allowed[row["chat_id"]].add(row["user_id"])

    # Восстанавливаем мьюты/баны из логов после рестарта (только последнее действие на пару user+chat)
    # Один запрос, без JOIN, читает только нужные action — не нагружает БД
    async with st.pool.acquire() as c:
        rows = await c.fetch("""
            SELECT DISTINCT ON (target_id, chat_id)
                target_id, chat_id, action, reason, ts, moderator_id
            FROM action_logs
            WHERE action IN ('MUTE','BAN_PERM','UNMUTE','UNBAN','SA_UNMUTE',
                             'TWIN_MUTE','TWIN_MUTE_MANUAL')
            ORDER BY target_id, chat_id, ts DESC
        """)
    for row in rows:
        a     = row["action"]
        cid   = row["chat_id"]
        uid_r = row["target_id"]
        meta  = {
            "reason": row["reason"] or "—",
            "ts":     row["ts"].timestamp() if row["ts"] else 0.0,
            "mod_id": row["moderator_id"] or 0,
            "until":  None,
        }
        if a in ("MUTE", "TWIN_MUTE", "TWIN_MUTE_MANUAL"):
            st.muted_users[cid].add(uid_r)
            st.mute_meta[cid][uid_r] = meta
        elif a == "BAN_PERM":
            st.banned_users[cid].add(uid_r)
            st.ban_meta[cid][uid_r] = meta
        elif a in ("UNMUTE", "UNBAN", "SA_UNMUTE"):
            st.muted_users[cid].discard(uid_r)
            st.banned_users[cid].discard(uid_r)
            st.mute_meta[cid].pop(uid_r, None)
            st.ban_meta[cid].pop(uid_r, None)
    # Восстанавливаем mat_silent_users из логов
    async with st.pool.acquire() as c:
        mat_rows = await c.fetch("""
            SELECT DISTINCT ON (target_id, chat_id) target_id, chat_id, action
            FROM action_logs
            WHERE action IN ('MAT_SILENT_ON', 'MAT_SILENT_OFF')
            ORDER BY target_id, chat_id, ts DESC
        """)
    for row in mat_rows:
        if row["action"] == "MAT_SILENT_ON":
            st.mat_silent_users.add((row["chat_id"], row["target_id"]))
        else:
            st.mat_silent_users.discard((row["chat_id"], row["target_id"]))
    # Восстанавливаем local_immune из логов
    async with st.pool.acquire() as c:
        imm_rows = await c.fetch("""
            SELECT DISTINCT ON (target_id, chat_id) target_id, chat_id, action
            FROM action_logs
            WHERE action IN ('UNBAN_LOCAL', 'UNMUTE_LOCAL', 'BAN_PERM', 'BAN_TEMP')
            ORDER BY target_id, chat_id, ts DESC
        """)
    for row in imm_rows:
        if row["action"] in ("UNBAN_LOCAL", "UNMUTE_LOCAL"):
            st.local_immune.add((row["chat_id"], row["target_id"]))
        elif row["action"] in ("BAN_PERM", "BAN_TEMP"):
            st.local_immune.discard((row["chat_id"], row["target_id"]))

    log.info(
        "DB ready | garants=%d mods=%d admins=%d twin_links=%d muted=%d banned=%d",
        len(st.garants), len(st.mods), len(st.admins),
        sum(len(v) for v in st.twins.values()),
        sum(len(v) for v in st.muted_users.values()),
        sum(len(v) for v in st.banned_users.values()),
    )


async def db_warns_get(chat_id: int, user_id: int) -> int:
    cached = st.warn_cache[chat_id].get(user_id)
    if cached is not None:
        return cached
    async with st.pool.acquire() as c:
        row = await c.fetchrow(
            "SELECT warns FROM warnings WHERE user_id=$1 AND chat_id=$2",
            user_id, chat_id,
        )
    count = row["warns"] if row else 0
    st.warn_cache[chat_id][user_id] = count
    return count


async def db_warns_add(chat_id: int, user_id: int, reason: str = "", mod_id: int = 0) -> int:
    async with st.pool.acquire() as c:
        row = await c.fetchrow(
            """
            INSERT INTO warnings (user_id, chat_id, warns, last_warn, reason)
            VALUES ($1, $2, 1, NOW(), $3)
            ON CONFLICT (user_id, chat_id)
            DO UPDATE SET warns = warnings.warns + 1, last_warn = NOW(), reason = $3
            RETURNING warns
            """,
            user_id, chat_id, reason,
        )
        count = row["warns"]
        await c.execute(
            "INSERT INTO warn_history (user_id, chat_id, warn_number, reason, moderator_id) "
            "VALUES ($1, $2, $3, $4, $5)",
            user_id, chat_id, count, reason, mod_id,
        )
    st.warn_cache[chat_id][user_id] = count
    return count


async def db_warns_reset(chat_id: int, user_id: int) -> None:
    async with st.pool.acquire() as c:
        await c.execute(
            "UPDATE warnings SET warns=0 WHERE user_id=$1 AND chat_id=$2",
            user_id, chat_id,
        )
    st.warn_cache[chat_id][user_id] = 0


async def db_log(action: str, mod_id: int, target_id: int, chat_id: int, reason: str = "") -> None:
    try:
        async with st.pool.acquire() as c:
            await c.execute(
                "INSERT INTO action_logs (action, moderator_id, target_id, chat_id, reason) "
                "VALUES ($1, $2, $3, $4, $5)",
                action, mod_id, target_id, chat_id, reason,
            )
    except Exception as e:
        log.warning("db_log failed: %s", e)


async def db_get_welcome(chat_id: int) -> Optional[str]:
    async with st.pool.acquire() as c:
        row = await c.fetchrow(
            "SELECT welcome_message FROM chat_settings WHERE chat_id=$1", chat_id
        )
    return row["welcome_message"] if row else None


async def db_set_welcome(chat_id: int, text: Optional[str]) -> None:
    async with st.pool.acquire() as c:
        await c.execute(
            "INSERT INTO chat_settings (chat_id, welcome_message) VALUES ($1, $2) "
            "ON CONFLICT (chat_id) DO UPDATE SET welcome_message = $2",
            chat_id, text,
        )


_SETTINGS_DEFAULTS: dict[str, bool] = {
    "antilink":        True,
    "antimat":         True,
    "antiescort":      True,
    "antiarabic":      True,
    "antifiles":       True,
    "antitwin":        True,
    "antiprofilespam": True,
    "antigambling":    True,
    "antibegging":     True,
    "antidoxx":        True,
    "antisuspicious":  True,
}

_SETTINGS_LABELS: dict[str, str] = {
    "antilink":        "\U0001f517 Анти-реклама (ссылки)",
    "antimat":         "\U0001f92c Анти-мат",
    "antiescort":      "\U0001f51e Анти-эскорт/18+",
    "antiarabic":      "\U0001f30d Анти-арабский текст",
    "antifiles":       "\U0001f4ce Удалять файлы",
    "antitwin":        "\U0001f465 Анти-твинк",
    "antiprofilespam": "\U0001f4e2 Анти-спам профиля",
    "antigambling":    "\U0001f3b0 Анти-азартные игры",
    "antibegging":     "\U0001f64f Анти-попрошайничество",
    "antidoxx":        "\U0001f575 Анти-докс/угрозы слива данных",
    "antisuspicious":  "\U00002753 Анти-сомнительные услуги",
}


def build_rules_text() -> str:
    """Строит текст правил из кэша (актуален после изменений)."""
    if not st.rules_cache:
        return "📜 <b>Правила чата Cz Гарант:</b>\n\n<i>Правила ещё не заданы.</i>"
    nums = ["1️⃣","2️⃣","3️⃣","4️⃣","5️⃣","6️⃣","7️⃣","8️⃣","9️⃣","🔟"]
    lines = ["📜 <b>Правила чата Cz Гарант:</b>\n"]
    for rule_num in sorted(st.rules_cache):
        r = st.rules_cache[rule_num]
        emoji = nums[rule_num - 1] if rule_num <= len(nums) else f"{rule_num}."
        action_str = (
            f"🚫 Бан <b>{r['duration_label']}</b>" if r["action"] == "ban"
            else f"🔇 Мут <b>{r['duration_label']}</b>"
        )
        lines.append(f"{emoji} <b>{r['description']}</b> → {action_str}")
    lines += [
        "",
        "🤝 Будьте вежливы и доброжелательны!",
        "⚠️ <i>Написал с твинка пока в муте → 🔇 Мут на твинк до снятия администрацией</i>",
        "",
        "🛡 <b>Вызов гаранта</b>",
        "",
        "• <b>Reply</b> на сообщение участника: <code>/адм текст сделки</code>",
        "• Укажите предмет сделки и сумму",
        "• У <b>обоих</b> участников должен быть <b>запущен бот</b>",
        "",
        "🧾 <b>Апелляция на наказание:</b>",
        "Если вы считаете мут/бан ошибочным — напишите боту в ЛС и нажмите кнопку «Подать апелляцию», "
        "затем опишите ситуацию одним сообщением.",
        "",
        "💬 <code>/админы</code> — список администрации",
    ]
    return "\n".join(lines)


async def db_get_settings(chat_id: int) -> dict[str, bool]:
    """Возвращает все настройки чата (с кэшем)."""
    cached = st.settings_cache.get(chat_id)
    if cached is not None:
        return cached
    async with st.pool.acquire() as c:
        row = await c.fetchrow("SELECT * FROM chat_settings WHERE chat_id=$1", chat_id)
    result = dict(_SETTINGS_DEFAULTS)
    if row:
        for key in _SETTINGS_DEFAULTS:
            val = row.get(key)
            if val is not None:
                result[key] = bool(val)
    st.settings_cache[chat_id] = result
    return result


async def db_set_setting(chat_id: int, key: str, value: bool) -> None:
    """Сохраняет одну настройку и обновляет кэш."""
    async with st.pool.acquire() as c:
        await c.execute(
            f"INSERT INTO chat_settings (chat_id, {key}) VALUES ($1, $2) "
            f"ON CONFLICT (chat_id) DO UPDATE SET {key} = $2",
            chat_id, value,
        )
    if chat_id in st.settings_cache:
        st.settings_cache[chat_id][key] = value
    else:
        st.settings_cache[chat_id] = {**_SETTINGS_DEFAULTS, key: value}


async def db_antilink_on(chat_id: int) -> bool:
    s = await db_get_settings(chat_id)
    return s.get("antilink", True)


async def db_ad_hit(chat_id: int, user_id: int) -> int:
    async with st.pool.acquire() as c:
        row = await c.fetchrow(
            """
            INSERT INTO automod_state (user_id, chat_id, ad_hits, last_ad)
            VALUES ($1, $2, 1, NOW())
            ON CONFLICT (user_id, chat_id)
            DO UPDATE SET ad_hits = automod_state.ad_hits + 1, last_ad = NOW()
            RETURNING ad_hits
            """,
            user_id, chat_id,
        )
    return int(row["ad_hits"])


def ad_mute_duration_by_hits(hits: int) -> tuple[int, str]:
    # За рекламу — сразу мут на 1 неделю, независимо от числа нарушений.
    return AD_MUTE_THIRD_SECS, AD_MUTE_THIRD_LABEL


async def allow_twin_user(chat_id: int, user_id: int, by: int = 0) -> None:
    """Разрешить твинку писать после ручного размута/разбана."""
    st.twin_allowed[chat_id].add(user_id)
    try:
        async with st.pool.acquire() as c:
            await c.execute(
                "INSERT INTO twin_allowlist (user_id, chat_id, allowed_by) VALUES ($1,$2,$3) "
                "ON CONFLICT (user_id, chat_id) DO UPDATE SET allowed_by=$3, added_at=NOW()",
                user_id, chat_id, by,
            )
    except Exception as e:
        log.warning("allow_twin_user failed: %s", e)


_ROLE_MAP: dict[str, tuple[str, set[int]]] = {
    "гаранта":        ("garant_admins", st.garants),
    "модератора":     ("moderators",    st.mods),
    "администратора": ("administrators", st.admins),
}


async def role_add(table: str, mem: set[int], user_id: int, username: str, by: int) -> None:
    async with st.pool.acquire() as c:
        await c.execute(
            "INSERT INTO {t} (user_id, username, added_by) VALUES ($1, $2, $3) "
            "ON CONFLICT (user_id) DO UPDATE SET username=$2, added_by=$3".format(t=table),
            user_id, username, by,
        )
    mem.add(user_id)


async def role_remove(table: str, mem: set[int], user_id: int) -> None:
    async with st.pool.acquire() as c:
        await c.execute(f"DELETE FROM {table} WHERE user_id=$1", user_id)
    mem.discard(user_id)


async def resolve_user(bot: Bot, chat_id: int, raw: str):
    raw = raw.lstrip("@").strip()
    try:
        target = int(raw) if raw.lstrip("-").isdigit() else f"@{raw}"
        cm     = await bot.get_chat_member(chat_id, target)
        return cm.user
    except Exception:
        return None


async def get_cached_garant_data() -> tuple[list[int], set[str]]:
    now_ts = time.monotonic()
    cached = st.role_name_cache.get("garants")
    if cached and now_ts - cached[0] <= 60:
        return cached[1], cached[2]
    async with st.pool.acquire() as c:
        rows = await c.fetch("SELECT user_id, username FROM garant_admins")
    ids = [row["user_id"] for row in rows]
    names = {row["username"].lower() for row in rows if row["username"]}
    st.role_name_cache["garants"] = (now_ts, ids, names)
    return ids, names


async def deliver_deal_link_private_only(deal_id: str, chat_id: int, deal_link: str, body: str) -> tuple[int, list[str]]:
    _garant_ids, garant_usernames = await get_cached_garant_data()
    delivered = 0
    failed_users: list[str] = []
    link_text = (
        f"🤝 Гарант готов провести вашу сделку!\n\n"
        f"🔗 Перейдите в гарант-чат: <a href='{deal_link}'>{esc(deal_link)}</a>"
    )

    # Сначала пробуем доставить по сохранённым uid (надёжно, без resolve)
    uid_list = st.deal_uids.get(deal_id, [])
    sent_uids: set[int] = set()
    for uid in uid_list:
        try:
            await bot.send_message(uid, link_text)
            delivered += 1
            sent_uids.add(uid)
            log.info("Ссылка по сделке %s доставлена uid=%s", deal_id, uid)
        except TelegramForbiddenError:
            log.warning("uid=%s заблокировал бота (сделка %s)", uid, deal_id)
            failed_users.append(f"<code>{uid}</code>")
        except Exception as e:
            log.warning("Не удалось отправить ссылку uid=%s: %s", uid, e)
            failed_users.append(f"<code>{uid}</code>")

    # Дополнительно — ищем @упоминания из текста сделки (fallback для username-режима)
    all_raw = _RE_MENTION.findall(body)
    for m_str in dict.fromkeys(all_raw):
        uname_clean = m_str.lstrip("@").lower()
        if uname_clean in garant_usernames:
            continue
        user = await resolve_user(bot, chat_id, uname_clean)
        if not user or user.id in sent_uids:
            continue
        try:
            await bot.send_message(user.id, link_text)
            delivered += 1
            sent_uids.add(user.id)
        except Exception:
            if f"@{uname_clean}" not in failed_users:
                failed_users.append(f"@{uname_clean}")

    return delivered, failed_users


def esc(text: str) -> str:
    return text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


import unicodedata

# Диапазоны стилизованных Unicode-букв (Mathematical Alphanumeric Symbols
# и похожие блоки), которые пользователи часто ставят в имя профиля:
# жирный, курсив, готика, моноширинный, "double-struck" и т.д.
_FANCY_RANGES = [
    (0x1D400, 0x1D7FF),  # Mathematical Alphanumeric Symbols
    (0x24B6, 0x24E9),    # Circled Latin letters
    (0xFF21, 0xFF5A),    # Fullwidth Latin letters
    (0x2100, 0x214F),    # Letterlike symbols (часть используется как стиль)
]


def normalize_fancy_name(name: str) -> str:
    """Приводит вычурные Unicode-шрифты в имени к обычным читаемым символам.

    Использует unicodedata NFKD-декомпозицию, которая для большинства
    математических/готических/moноширинных латинских букв корректно
    возвращает обычный ASCII-эквивалент. Символы вне известных диапазонов
    и не входящие в декомпозицию оставляются как есть (например, эмодзи,
    кириллица без спецстиля).
    """
    result_chars = []
    for ch in name:
        code = ord(ch)
        is_fancy = any(lo <= code <= hi for lo, hi in _FANCY_RANGES)
        if is_fancy:
            decomposed = unicodedata.normalize("NFKD", ch)
            # Оставляем только базовые ASCII/буквенные символы из декомпозиции
            base = "".join(c for c in decomposed if not unicodedata.combining(c))
            result_chars.append(base if base else ch)
        else:
            result_chars.append(ch)
    return "".join(result_chars)


def mention(user) -> str:
    raw_name = user.first_name or "Пользователь"
    name = esc(normalize_fancy_name(raw_name))
    return f'<a href="tg://user?id={user.id}">{name}</a>'


def mention_by_id(user_id: int, name: str) -> str:
    return f'<a href="tg://user?id={user_id}">{esc(normalize_fancy_name(name))}</a>'


def _msg_link(chat_id: int, message_id: int) -> str:
    """Строит ссылку на сообщение в супергруппе (открывается у любого участника чата)."""
    cid = str(chat_id)
    cid = cid[4:] if cid.startswith("-100") else cid.lstrip("-")
    return f"https://t.me/c/{cid}/{message_id}"


async def _uid_display_link(bot: Bot, chat_id: int, user_id: int) -> str:
    """Кликабельная ссылка на профиль по user_id с именем, если удалось его узнать."""
    try:
        member = await bot.get_chat_member(chat_id, user_id)
        name = member.user.first_name or str(user_id)
        return mention_by_id(user_id, name)
    except Exception:
        return mention_by_id(user_id, str(user_id))


async def is_chat_admin(bot: Bot, chat_id: int, user_id: int) -> bool:
    if user_id in SUPER_ADMINS:
        return True
    now_ts = time.monotonic()
    cache_key = (chat_id, user_id)
    cached = st.chat_admin_cache.get(cache_key)
    if cached and now_ts - cached[0] <= 30:
        return cached[1]
    try:
        m = await bot.get_chat_member(chat_id, user_id)
        result = m.status in (ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.CREATOR)
    except Exception:
        result = False
    st.chat_admin_cache[cache_key] = (now_ts, result)
    return result


def is_bot_admin(user_id: int) -> bool:
    return (
        user_id in SUPER_ADMINS
        or user_id in st.garants
        or user_id in st.mods
        or user_id in st.admins
    )


async def safe_delete(msg: Message) -> None:
    try:
        await msg.delete()
    except (TelegramBadRequest, TelegramForbiddenError):
        pass


async def send_auto_notif(chat_id: int, text: str, delay: int = 180) -> None:
    """Отправляет уведомление об авто-действии в чат и удаляет его через delay секунд."""
    try:
        sent = await bot.send_message(chat_id, text)
        await asyncio.sleep(delay)
        try:
            await sent.delete()
        except Exception:
            pass
    except Exception as e:
        log.warning("send_auto_notif failed: %s", e)


async def mute_user(
    bot: Bot, chat_id: int, user_id: int,
    seconds: Optional[int] = None,
    reason: str = "", mod_id: int = 0,
) -> None:
    """seconds=None → бессрочный мут. reason/mod_id — для отображения в панели."""
    until = datetime.now(timezone.utc) + timedelta(seconds=seconds) if seconds else None
    await bot.restrict_chat_member(
        chat_id, user_id,
        permissions=ChatPermissions(can_send_messages=False),
        until_date=until,
    )
    st.muted_users[chat_id].add(user_id)
    st.mute_meta[chat_id][user_id] = {
        "reason": reason or "—",
        "ts": time.time(),
        "mod_id": mod_id,
        "until": until.timestamp() if until else None,
    }
    remember_recent_punishment(chat_id, user_id, "mute")


async def unmute_user(bot: Bot, chat_id: int, user_id: int) -> None:
    await bot.restrict_chat_member(
        chat_id, user_id,
        permissions=ChatPermissions(
            can_send_messages=True,
            can_send_media_messages=True,
            can_send_polls=True,
            can_send_other_messages=True,
            can_add_web_page_previews=True,
            can_invite_users=True,
        ),
    )
    st.muted_users[chat_id].discard(user_id)
    st.mute_meta[chat_id].pop(user_id, None)


async def get_user_punishment_state(bot: Bot, chat_id: int, user_id: int) -> tuple[bool, bool]:
    """Возвращает (is_muted, is_banned) по кэшу и фактическому статусу в чате."""
    is_banned = user_id in st.banned_users.get(chat_id, set())
    is_muted = user_id in st.muted_users.get(chat_id, set())
    try:
        cm = await bot.get_chat_member(chat_id, user_id)
        if cm.status == ChatMemberStatus.KICKED:
            is_banned = True
            st.banned_users[chat_id].add(user_id)
        elif cm.status == ChatMemberStatus.RESTRICTED:
            if not cm.permissions or not cm.permissions.can_send_messages:
                is_muted = True
                st.muted_users[chat_id].add(user_id)
    except Exception:
        pass
    return is_muted, is_banned


def remember_recent_punishment(chat_id: int, user_id: int, kind: str) -> None:
    now_ts = time.monotonic()
    items = st.recent_punishments[chat_id]
    items.append((user_id, now_ts, kind))
    st.recent_punishments[chat_id] = [x for x in items if now_ts - x[1] <= 86400][-200:]


def find_recent_related_punishment(chat_id: int, user_id: int) -> Optional[tuple[int, str]]:
    now_ts = time.monotonic()
    # Если user_id является оригиналом — не трогаем
    if user_id in st.twins and user_id not in st.twin_of:
        return None
    # Иммунитет «разбан здесь» / «размут здесь» — авто-наказания не применяем
    if (chat_id, user_id) in st.local_immune:
        return None
    for orig_uid, ts, kind in reversed(st.recent_punishments.get(chat_id, [])):
        if orig_uid == user_id:
            continue
        if now_ts - ts > 86400:
            continue
        # Только если user_id является твинком orig_uid (направленная связь),
        # а не наоборот — чтобы оригинал не попал под санкции твинка.
        if user_id in st.twin_of and orig_uid in st.twin_of[user_id]:
            return orig_uid, kind
    return None


# ══════════════════════════════════════════════════════════
# ГЛАВНАЯ ФУНКЦИЯ ПРОВЕРКИ РЕКЛАМНЫХ ССЫЛОК
# ══════════════════════════════════════════════════════════

def _extract_username_from_tg_url(url: str) -> Optional[str]:
    """Извлекает username из Telegram-ссылки."""
    m = re.search(
        r"(?:t\.me|telegram\.me|telegram\.dog)/([a-zA-Z][a-zA-Z0-9_]{0,31})",
        url, re.IGNORECASE,
    )
    return m.group(1).lower() if m else None


def _is_own_link(url_or_username: str) -> bool:
    """Проверяет, является ли ссылка ссылкой на наш чат или бота."""
    uname = url_or_username.lower().lstrip("@")
    # Убираем путь если есть
    uname = uname.split("/")[0]
    if uname in OWN_CHAT_USERNAMES:
        return True
    if BOT_USERNAME and uname == BOT_USERNAME.lower():
        return True
    return False


def has_ad_link(text: str, entities) -> tuple[bool, str]:
    """
    Проверяет наличие запрещённых Telegram-ссылок/инвайтов.

    Важно для гаранта-чата:
    • обычные @username продавцов/покупателей НЕ считаются рекламой;
    • ссылки НЕ Telegram разрешены;
    • @username ловится только при явном рекламном контексте канала/чата;
    • сообщения формата сделки не трогаем.
    """
    text = text or ""
    text_lower = text.lower()
    deal_like = any(w in text_lower for w in _DEAL_WORDS)

    def is_tg_url(value: str) -> bool:
        v = (value or "").lower()
        return any(d in v for d in ("t.me", "telegram.me", "telegram.dog")) or bool(_RE_TG_SCHEME.search(v))

    # ── 1. Entities от Telegram ───────────────────────────
    for ent in (entities or []):
        if ent.type == "url" and text:
            url_text = text[ent.offset: ent.offset + ent.length]
            url_lower = url_text.lower()

            # Все НЕ Telegram ссылки разрешены
            if not is_tg_url(url_lower):
                continue

            if _RE_TG_SCHEME.search(url_lower):
                return True, "tg:// ссылка"

            uname = _extract_username_from_tg_url(url_lower)
            if uname and _is_own_link(uname):
                continue
            if "/+" in url_lower or "/joinchat/" in url_lower:
                return True, "приватная ссылка на Telegram-чат"
            if uname:
                return True, f"Telegram-ссылка на @{uname}"
            return True, "Telegram-ссылка"

        elif ent.type == "text_link" and ent.url:
            url_lower = ent.url.lower()

            # Все НЕ Telegram ссылки разрешены
            if not is_tg_url(url_lower):
                continue

            if _RE_TG_SCHEME.search(url_lower):
                return True, "скрытая tg:// ссылка"

            uname = _extract_username_from_tg_url(url_lower)
            if uname and _is_own_link(uname):
                continue
            if "/+" in url_lower or "/joinchat/" in url_lower:
                return True, "скрытая приватная Telegram-ссылка"
            return True, "скрытая Telegram-ссылка"

        elif ent.type == "mention" and text:
            # Для сделок обычные @username разрешены
            if deal_like:
                continue

            username = text[ent.offset + 1: ent.offset + ent.length].lower()
            if _is_own_link(username):
                continue

            ctx_start = max(0, ent.offset - 70)
            ctx_end   = min(len(text), ent.offset + ent.length + 70)
            context   = text[ctx_start:ctx_end]

            # Не любой рекламный контекст, а именно контекст чата/канала/группы
            if _AD_CONTEXT_WORDS.search(context) and re.search(r"чат|канал|групп|channel|join|subscribe", context, re.I):
                return True, f"реклама Telegram-канала/чата @{username}"

    # ── 2. Regex по тексту ────────────────────────────────
    if text:
        for m in _RE_TG_LINKS.finditer(text):
            url    = m.group(0)
            url_lo = url.lower()

            # telegra.ph и любые НЕ t.me/telegram ссылки не наказываем
            if "telegra.ph" in url_lo:
                continue

            uname = _extract_username_from_tg_url(url)
            if uname and _is_own_link(uname):
                continue

            if re.search(r"/(?:\+|joinchat/)", url_lo, re.I):
                return True, "приватная ссылка на Telegram-чат"
            if uname:
                return True, f"Telegram-ссылка на @{uname}"
            return True, "Telegram-ссылка"

        if _RE_TG_SCHEME.search(text):
            return True, "tg:// ссылка"

        if _RE_MASKED_TG.search(text):
            return True, "замаскированная Telegram-ссылка"

        # @username без entity: только если это НЕ сделка и явно рекламируют чат/канал
        if not deal_like:
            for m in _RE_AT_MENTION.finditer(text):
                username = m.group(1).lower()
                if _is_own_link(username):
                    continue
                ctx_start = max(0, m.start() - 70)
                ctx_end   = min(len(text), m.end() + 70)
                context   = text[ctx_start:ctx_end]
                if _AD_CONTEXT_WORDS.search(context) and re.search(r"чат|канал|групп|channel|join|subscribe", context, re.I):
                    return True, f"реклама Telegram-канала/чата @{username}"

    return False, ""


def parse_reason(raw: str) -> str:
    s = raw.strip()
    if s.isdigit():
        n = int(s)
        # Сначала смотрим в живой кэш правил (обновляемых через панель)
        r = st.rules_cache.get(n) or {}
        desc = r.get("description") or RULE_REASONS.get(n)
        if desc:
            return f"Правило {n}: {desc}"
    return s or "не указана"


def extract_uid_from_bot_msg(msg: Message) -> Optional[int]:
    for ent in (msg.entities or msg.caption_entities or []):
        if ent.type == "text_link" and ent.url:
            m = re.search(r"tg://user\?id=(\d+)", ent.url)
            if m:
                return int(m.group(1))
    text = msg.text or msg.caption or ""
    m = re.search(r"uid:(\d+)", text)
    if m:
        return int(m.group(1))
    return None


def make_deleted_message_preview(msg: Message, max_len: int = 1800) -> str:
    """Готовит текст удалённого сообщения для ЛС модераторам."""
    text = msg.text or msg.caption or ""
    parts: list[str] = []

    if text:
        parts.append(f"🗑 <b>Удалённое сообщение:</b>\n<blockquote>{esc(text[:max_len])}</blockquote>")
    else:
        media_type = "медиа/файл"
        for attr, label in (
            ("sticker", "стикер"),
            ("photo", "фото"),
            ("video", "видео"),
            ("animation", "GIF"),
            ("document", "документ"),
            ("voice", "голосовое"),
            ("video_note", "кружок"),
        ):
            if getattr(msg, attr, None):
                media_type = label
                break
        parts.append(f"🗑 <b>Удалено сообщение без текста:</b> <i>{esc(media_type)}</i>")

    ent_lines: list[str] = []
    for ent in list(msg.entities or []) + list(msg.caption_entities or []):
        if ent.type == "text_link" and ent.url:
            ent_lines.append(f"• text_link: <code>{esc(ent.url)}</code>")
        elif ent.type in ("url", "mention") and text:
            raw = text[ent.offset: ent.offset + ent.length]
            ent_lines.append(f"• {ent.type}: <code>{esc(raw)}</code>")
    if ent_lines:
        parts.append("🔗 <b>Entities:</b>\n" + "\n".join(ent_lines[:10]))

    return "\n\n".join(parts)


def _text_hash(text: str) -> str:
    normalized = re.sub(r"\s+", " ", text.strip().lower())
    return hashlib.md5(normalized.encode()).hexdigest()


# Хранилище хэшей сообщений для детектора твинков: chat_id -> {hash -> (uid, is_banned)}
# Хранится для ЛЮБОГО достаточно длинного сообщения (не только нарушителей),
# чтобы твинк ловился, даже если оригинал ничего не нарушил.
# OrderedDict + лимит размера на чат — иначе память росла бы бесконечно
# в активных чатах (запись на каждое сообщение, без TTL).
_VIOLATION_HASHES_MAX_PER_CHAT = 5000
_violation_hashes: dict[int, "OrderedDict[str, tuple[int, bool]]"] = defaultdict(OrderedDict)


_AUTO_BAN_LOG_MAX = 300


def _log_auto_ban(chat_id: int, chat_title: str, uid: int, name: str, reason: str) -> None:
    st.auto_ban_log.append({
        "chat_id": chat_id,
        "chat_title": chat_title,
        "uid": uid,
        "name": name,
        "reason": reason,
        "ts": time.time(),
    })
    if len(st.auto_ban_log) > _AUTO_BAN_LOG_MAX:
        del st.auto_ban_log[: len(st.auto_ban_log) - _AUTO_BAN_LOG_MAX]


def _remember_text_hash(chat_id: int, th: str, uid: int, is_banned: bool) -> None:
    vh = _violation_hashes[chat_id]
    vh[th] = (uid, is_banned)
    vh.move_to_end(th)
    while len(vh) > _VIOLATION_HASHES_MAX_PER_CHAT:
        vh.popitem(last=False)


async def check_twin_by_text(
    bot: Bot,
    msg: Message,
    uid: int,
    chat_id: int,
    text: str,
) -> bool:
    if len(text) < TWIN_MIN_LEN:
        return False

    th = _text_hash(text)

    # Прощено именно ЭТО сообщение (или полностью идентичный текст) —
    # но другой текст, совпадающий с чужим сообщением, всё равно поймает твинк-детектор.
    if (chat_id, uid, th) in st.hash_pardons:
        return False

    vh = _violation_hashes[chat_id]

    orig_uid = None
    if th in vh:
        cached_uid, _orig_banned = vh[th]
        if cached_uid != uid:
            orig_uid = cached_uid

    if orig_uid is None and uid not in st.twin_allowed.get(chat_id, set()):
        # Для юзеров, которых админ явно простил (кнопка "Размутить/Разбанить"),
        # больше не мутим по общему таймеру наказаний — только по честному
        # совпадению текста с сообщением другого реального человека (ниже).
        recent = find_recent_related_punishment(chat_id, uid)
        if recent:
            orig_uid, _kind = recent

    if orig_uid is not None:
        # Сначала пересылаем модераторам (с premium emoji), потом удаляем
        try:
            orig_member = await bot.get_chat_member(chat_id, orig_uid)
            orig_name = orig_member.user.first_name or str(orig_uid)
        except Exception:
            orig_name = str(orig_uid)
        user_name  = msg.from_user.first_name or str(uid)
        chat_title = msg.chat.title or str(chat_id)
        twin_header = (
            f"👥 <b>Авто-твинк по тексту — мут</b>\n\n"
            f"💬 Чат: <b>{esc(chat_title)}</b>\n"
            f"👤 {mention_by_id(uid, user_name)} (<code>{uid}</code>)\n"
            f"🔗 Твинк: {mention_by_id(orig_uid, orig_name)} (<code>{orig_uid}</code>)\n\n"
            f"⬇️ Сообщение (удалено):"
        )
        recipients_twin: list[int] = list(SUPER_ADMINS)
        async with st.pool.acquire() as _mc:
            _mrows = await _mc.fetch("SELECT user_id FROM moderators")
        _seen_twin: set[int] = set(SUPER_ADMINS)
        for _row in _mrows:
            if _row["user_id"] not in _seen_twin:
                recipients_twin.append(_row["user_id"])
                _seen_twin.add(_row["user_id"])
        twin_caption = (
            f"👥 <b>Авто-твинк по тексту — мут</b>\n\n"
            f"💬 Чат: <b>{esc(chat_title)}</b>\n"
            f"👤 {mention_by_id(uid, user_name)} (<code>{uid}</code>)\n"
            f"🔗 Твинк: {mention_by_id(orig_uid, orig_name)} (<code>{orig_uid}</code>)"
        )
        for _admin_id in recipients_twin:
            try:
                await bot.copy_message(
                    chat_id=_admin_id,
                    from_chat_id=chat_id,
                    message_id=msg.message_id,
                    caption=twin_caption,
                )
            except Exception:
                try:
                    await bot.send_message(_admin_id, twin_caption)
                except Exception:
                    pass
        await safe_delete(msg)
        try:
            await mute_user(bot, chat_id, uid, None)
        except Exception:
            pass
        st.muted_users[chat_id].add(uid)
        try:
            async with st.pool.acquire() as _c:
                await _c.execute(
                    "INSERT INTO twin_accounts (user_id, twin_of, chat_id, added_by) "
                    "VALUES ($1,$2,$3,$4) ON CONFLICT (user_id, twin_of, chat_id) DO NOTHING",
                    uid, orig_uid, chat_id, 0,
                )
        except Exception as _e:
            log.warning("Не удалось сохранить твинк в БД: %s", _e)
        st.twins[orig_uid].add(uid)
        st.twin_of[uid].add(orig_uid)
        await db_log("TWIN_MUTE", 0, uid, chat_id, f"Твинк {orig_uid} (авто по тексту)")
        asyncio.create_task(send_auto_notif(
            chat_id,
            f"⚠️ Обнаружен твинк — совпадающий текст.\n"
            f"🔇 {mention(msg.from_user)} — мут <b>до снятия администрацией</b>.\n"
            f"<code>uid:{uid}</code>" + APPEAL_HINT,
        ))
        await notify_auto_action(
            bot=bot,
            chat_id=chat_id,
            chat_title=msg.chat.title or "Группа",
            target_id=uid,
            target_name=user_name,
            action="🔇 Мут навсегда, до решения администрации (авто-твинк по тексту)",
            reason="Идентичный текст сообщения другого пользователя",
            duration="до снятия администрацией",
            deleted_preview=make_deleted_message_preview(msg),
            msg_hash=th,
            related_id=orig_uid,
            related_name=orig_name,
        )
        return True

    # Регистрируем хэш ЛЮБОГО достаточно длинного сообщения — не только
    # нарушителей — чтобы твинк ловился даже если оригинал ничего не нарушал
    # и не был замьючен админом.
    if th not in vh:
        is_muted, is_banned = await get_user_punishment_state(bot, chat_id, uid)
        _remember_text_hash(chat_id, th, uid, is_banned)

    return False


async def check_manual_twins(
    bot: Bot,
    msg: Message,
    uid: int,
    chat_id: int,
) -> bool:
    if uid in st.twin_allowed.get(chat_id, set()):
        return False
    # Иммунитет «разбан здесь» / «размут здесь» — не трогаем в этом чате
    if (chat_id, uid) in st.local_immune:
        return False
    # Используем направленную связь: uid является твинком кого-то
    if uid not in st.twin_of:
        return False

    # Мьютим по факту пометки — вне зависимости от текущего статуса оригинала
    orig_uid  = next(iter(st.twin_of[uid]))
    user_name = msg.from_user.first_name or str(uid)
    chat_title = msg.chat.title or str(chat_id)
    try:
        orig_member = await bot.get_chat_member(chat_id, orig_uid)
        orig_name = orig_member.user.first_name or str(orig_uid)
    except Exception:
        orig_name = str(orig_uid)
    # Форвард модераторам с premium emoji до удаления
    twin_header = (
        f"👥 <b>Твинк — ручная пометка — мут</b>\n\n"
        f"💬 Чат: <b>{esc(chat_title)}</b>\n"
        f"👤 {mention_by_id(uid, user_name)} (<code>{uid}</code>)\n"
        f"🔗 Твинк: {mention_by_id(orig_uid, orig_name)} (<code>{orig_uid}</code>)\n\n"
        f"⬇️ Сообщение (удалено):"
    )
    recipients_twin: list[int] = list(SUPER_ADMINS)
    async with st.pool.acquire() as _mc:
        _mrows = await _mc.fetch("SELECT user_id FROM moderators")
    _seen_twin: set[int] = set(SUPER_ADMINS)
    for _row in _mrows:
        if _row["user_id"] not in _seen_twin:
            recipients_twin.append(_row["user_id"])
            _seen_twin.add(_row["user_id"])
    twin_caption2 = (
        f"👥 <b>Твинк — ручная пометка — мут</b>\n\n"
        f"💬 Чат: <b>{esc(chat_title)}</b>\n"
        f"👤 {mention_by_id(uid, user_name)} (<code>{uid}</code>)\n"
        f"🔗 Твинк: {mention_by_id(orig_uid, orig_name)} (<code>{orig_uid}</code>)"
    )
    for _admin_id in recipients_twin:
        try:
            await bot.copy_message(
                chat_id=_admin_id,
                from_chat_id=chat_id,
                message_id=msg.message_id,
                caption=twin_caption2,
            )
        except Exception:
            try:
                await bot.send_message(_admin_id, twin_caption2)
            except Exception:
                pass
    await safe_delete(msg)
    try:
        await mute_user(bot, chat_id, uid, None)
    except Exception:
        pass
    st.muted_users[chat_id].add(uid)
    await db_log("TWIN_MUTE", 0, uid, chat_id, f"Твинк нарушителя {orig_uid} (ручная пометка)")
    asyncio.create_task(send_auto_notif(
        chat_id,
        f"⚠️ Аккаунт помечен как твинк нарушителя.\n"
        f"🔇 {mention(msg.from_user)} — мут <b>до снятия администрацией</b>.\n"
        f"<code>uid:{uid}</code>" + APPEAL_HINT,
    ))
    await notify_auto_action(
        bot=bot,
        chat_id=chat_id,
        chat_title=msg.chat.title or "Группа",
        target_id=uid,
        target_name=user_name,
        action="🔇 Мут навсегда, до решения администрации (твинк, ручная пометка)",
        reason="Помечен твинком нарушителя",
        duration="до снятия администрацией",
        deleted_preview=make_deleted_message_preview(msg),
        related_id=orig_uid,
        related_name=orig_name,
    )
    return True


async def get_participant_mentions(
bot: Bot, chat_id: int, body: str, garant_usernames: set[str]) -> list[str]:
    all_mentions = _RE_MENTION.findall(body)
    unique = list(dict.fromkeys(all_mentions))
    participants_mentions = []
    for m in unique:
        uname_clean = m.lstrip("@").lower()
        if uname_clean in garant_usernames:
            continue
        user = await resolve_user(bot, chat_id, uname_clean)
        if user:
            name = esc(user.first_name or uname_clean)
            participants_mentions.append(f'<a href="tg://user?id={user.id}">{name}</a>')
        else:
            participants_mentions.append(f"@{uname_clean}")
    return participants_mentions


# ─────────────────────────────────────────────────────────
# УВЕДОМЛЕНИЕ ОБ АВТО-ДЕЙСТВИЯХ
# ─────────────────────────────────────────────────────────

async def _notify_mat(bot: Bot, msg: Message, chat_id: int, uid: int, msg_hash: str) -> None:
    """Удаляет матерное сообщение сразу, пересылает модераторам для решения.
    Кнопки:
      «🗑 Удалять впредь» — бот молча удаляет все матерные от этого юзера, без форварда
      «👌 Не реагировать» — конкретно этот форвард проигнорирован, следующее снова пришлёт
    Премиум-эмодзи и форматирование сохраняются через forward (до удаления).
    """
    import uuid
    notif_id  = uuid.uuid4().hex[:8]
    user_name  = msg.from_user.first_name or str(uid)
    chat_title = msg.chat.title or str(chat_id)

    # Сначала пересылаем — потом удаляем (иначе forward упадёт)
    recipients: list[int] = list(SUPER_ADMINS)
    async with st.pool.acquire() as c:
        mod_rows = await c.fetch("SELECT user_id FROM moderators")
    seen = set(SUPER_ADMINS)
    for row in mod_rows:
        if row["user_id"] not in seen:
            recipients.append(row["user_id"])
            seen.add(row["user_id"])

    cb_silent = f"mat_silent:{notif_id}:{chat_id}:{uid}"
    cb_ignore  = f"mat_ign:{notif_id}:{chat_id}:{uid}"
    kb = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="🔇 Удалять впредь", callback_data=cb_silent),
        InlineKeyboardButton(text="👌 Не реагировать", callback_data=cb_ignore),
    ]])

    # caption = заголовок + инфо о юзере, прикрепляется прямо к скопированному сообщению
    caption = (
        f"🤬 <b>Мат/оскорбление — удалено</b>\n\n"
        f"💬 Чат: <b>{esc(chat_title)}</b>\n"
        f"👤 {mention_by_id(uid, user_name)} (<code>{uid}</code>)\n\n"
        f"☝️ Что делать с этим пользователем?"
    )

    notif_msg_ids: list[tuple[int, int]] = []
    for admin_id in recipients:
        try:
            # copy_message позволяет добавить caption и кнопки прямо на само сообщение
            # premium emoji, стикеры, медиа — всё сохраняется
            sent = await bot.copy_message(
                chat_id=admin_id,
                from_chat_id=chat_id,
                message_id=msg.message_id,
                caption=caption,
                reply_markup=kb,
            )
            notif_msg_ids.append((admin_id, sent.message_id))
        except TelegramForbiddenError:
            log.warning("mat_notify: admin %s заблокировал бота", admin_id)
        except Exception as e:
            log.warning("mat_notify: не удалось уведомить %s: %s", admin_id, e)
            # Fallback: если copy_message не сработал (напр. стикер без caption)
            # шлём заголовок + forward отдельно
            try:
                await bot.forward_message(
                    chat_id=admin_id,
                    from_chat_id=chat_id,
                    message_id=msg.message_id,
                )
                sent_kb = await bot.send_message(
                    admin_id,
                    f"🤬 <b>Мат/оскорбление — удалено</b>\n"
                    f"💬 {esc(chat_title)} · 👤 {mention_by_id(uid, user_name)} (<code>{uid}</code>)",
                    reply_markup=kb,
                )
                notif_msg_ids.append((admin_id, sent_kb.message_id))
            except Exception as e2:
                log.warning("mat_notify fallback: %s", e2)

    # Удаляем из чата ПОСЛЕ форварда, потом пишем предупреждение
    await safe_delete(msg)
    try:
        await bot.send_message(
            chat_id,
            f"🤐 {mention_by_id(uid, user_name)}, не ругайся — уважай других участников! 🤝",
        )
    except Exception as _e:
        log.warning("mat notify: не смог написать в чат: %s", _e)

    st.mat_pending[notif_id] = {
        "chat_id":       chat_id,
        "message_id":    msg.message_id,
        "uid":           uid,
        "msg_hash":      msg_hash,
        "notif_msg_ids": notif_msg_ids,
        "ts":            time.time(),
    }
    if msg_hash:
        st.notif_hash[notif_id] = msg_hash
    await db_log("MAT_DELETE_AUTO", 0, uid, chat_id, "Авто-удаление мата (первый раз)")


async def _mat_close_notifs(bot: Bot, notif_id: str, result_text: str) -> None:
    """Обновляет кнопки у всех модераторов после принятия решения."""
    data = st.mat_pending.pop(notif_id, None)
    if not data:
        return
    for admin_id, kb_msg_id in data.get("notif_msg_ids", []):
        try:
            await bot.edit_message_text(
                result_text,
                chat_id=admin_id,
                message_id=kb_msg_id,
            )
        except Exception:
            pass


async def _notify_doxx_threat(
    bot: Bot, msg: Message, chat_id: int, uid: int, msg_hash: str, reason: str,
) -> None:
    """Угроза докса/слива данных — считаем 'тяжёлым' нарушением без чёткого
    авто-наказания: бот мьютит пользователя НАВСЕГДА и пересылает
    супер-админам/модераторам профиль + историю последних сообщений,
    чтобы они решили — забанить или снять (ложное срабатывание)."""
    import uuid
    notif_id  = uuid.uuid4().hex[:8]
    user_name = msg.from_user.first_name or str(uid)
    chat_title = msg.chat.title or str(chat_id)

    recipients: list[int] = list(SUPER_ADMINS)
    async with st.pool.acquire() as c:
        mod_rows = await c.fetch("SELECT user_id FROM moderators")
    seen = set(SUPER_ADMINS)
    for row in mod_rows:
        if row["user_id"] not in seen:
            recipients.append(row["user_id"])
            seen.add(row["user_id"])

    # История последних сообщений юзера в чате, КРОМЕ текущего (оно уже показано ниже)
    hist_ids = list(st.recent_msgs.get(chat_id, {}).get(uid, deque()))[:-1][-5:]
    hist_str = ""
    if hist_ids:
        links = " · ".join(
            f"<a href='{_msg_link(chat_id, mid)}'>#{i + 1}</a>" for i, mid in enumerate(hist_ids)
        )
        hist_str = f"📚 Последние сообщения в чате: {links}\n"

    deleted_preview = make_deleted_message_preview(msg)

    cb_base = f"{notif_id}:{chat_id}:{uid}"
    kb = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="🚫 Забанить", callback_data=f"doxx_ban:{cb_base}"),
        InlineKeyboardButton(text="🔊 Ложное срабатывание", callback_data=f"doxx_unmute:{cb_base}"),
    ]])

    text_notif = (
        f"🕵️ <b>Угроза доксом/сливом данных — авто-мут НАВСЕГДА</b>\n\n"
        f"💬 Чат: <b>{esc(chat_title)}</b>\n"
        f"👤 Профиль: {mention_by_id(uid, user_name)} (<code>{uid}</code>)\n"
        f"📝 {esc(reason)}\n"
        f"{hist_str}\n"
        f"{deleted_preview}\n\n"
        f"☝️ Решите: подтвердить бан или снять мут (ложное срабатывание)?"
    )

    # Мьютим сразу — до пересылки, чтобы не терять время
    try:
        await mute_user(bot, chat_id, uid, seconds=None, reason=reason)
    except Exception:
        pass

    notif_msg_ids: list[tuple[int, int]] = []
    for admin_id in recipients:
        try:
            sent = await bot.send_message(admin_id, text_notif, reply_markup=kb)
            notif_msg_ids.append((admin_id, sent.message_id))
        except TelegramForbiddenError:
            log.warning("doxx_notify: admin %s заблокировал бота", admin_id)
        except Exception as e:
            log.warning("doxx_notify: не удалось уведомить %s: %s", admin_id, e)

    await safe_delete(msg)

    st.doxx_pending[notif_id] = {
        "chat_id": chat_id,
        "uid": uid,
        "msg_hash": msg_hash,
        "notif_msg_ids": notif_msg_ids,
        "ts": time.time(),
    }
    if msg_hash:
        st.notif_hash[notif_id] = msg_hash
    await db_log("AUTO_MUTE_SEVERE", 0, uid, chat_id, reason)


async def _doxx_close_notifs(bot: Bot, notif_id: str, result_text: str) -> None:
    """Заменяет текст ВСЕХ уведомлений (у всех модераторов/супер-админов) по докс-угрозе
    на итог решения и убирает кнопки — по образцу _mat_close_notifs."""
    data = st.doxx_pending.pop(notif_id, None)
    if not data:
        return
    for admin_id, kb_msg_id in data.get("notif_msg_ids", []):
        try:
            await bot.edit_message_text(
                result_text,
                chat_id=admin_id,
                message_id=kb_msg_id,
                reply_markup=None,
            )
        except Exception:
            pass


async def notify_auto_action(
    bot: Bot,
    chat_id: int,
    chat_title: str,
    target_id: int,
    target_name: str,
    action: str,
    reason: str,
    duration: str,
    deleted_preview: str = "",
    msg_hash: str = "",
    related_id: Optional[int] = None,
    related_name: Optional[str] = None,
) -> None:
    import uuid
    notif_id = uuid.uuid4().hex[:8]
    dur_str = f"⏱ Срок: <b>{duration}</b>\n" if duration else ""
    preview_str = f"\n{deleted_preview}\n" if deleted_preview else ""
    related_str = (
        f"🔗 Совпадает с: {mention_by_id(related_id, related_name or str(related_id))} "
        f"(<code>{related_id}</code>)\n"
        if related_id else ""
    )

    # Храним хэш отдельно от callback_data — он не влезает в лимит Telegram 64 байта
    if msg_hash:
        st.notif_hash[notif_id] = msg_hash

    st.pending_auto_mutes[notif_id] = {
        "chat_id": chat_id,
        "chat_title": chat_title,
        "target_id": target_id,
        "target_name": target_name,
        "action": action,
        "reason": reason,
        "ts": time.time(),
    }

    # Кодируем в callback: notif_id:chat_id:target_id
    cb_base = f"{notif_id}:{chat_id}:{target_id}"

    kb = InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(
                text="🔊 Размутить/Разбанить",
                callback_data=f"sa_unmute:{cb_base}",
            ),
            InlineKeyboardButton(
                text="🔇 Оставить",
                callback_data=f"sa_keep:{cb_base}",
            ),
        ],
        [
            InlineKeyboardButton(
                text="🤖 Авто-действия",
                callback_data=f"autopanel:mute:{chat_id}",
            ),
        ],
    ])

    # Одно сообщение для всех — SA и моды получают одинаковый текст с кнопками
    text_notif = (
        f"🤖 <b>Авто-действие бота</b>\n\n"
        f"💬 Чат: <b>{esc(chat_title)}</b>\n"
        f"👤 <a href='tg://user?id={target_id}'>{esc(target_name)}</a> "
        f"(<code>{target_id}</code>)\n"
        f"⚡ <b>{action}</b>\n"
        f"{dur_str}"
        f"📝 <i>{esc(reason)}</i>\n"
        f"{related_str}"
        f"{preview_str}"
    )

    async with st.pool.acquire() as c:
        mod_rows = await c.fetch("SELECT user_id FROM moderators")

    notified_ids: set[int] = set()
    for recv_id in list(SUPER_ADMINS) + [r["user_id"] for r in mod_rows]:
        if recv_id in notified_ids:
            continue
        notified_ids.add(recv_id)
        try:
            await bot.send_message(recv_id, text_notif, reply_markup=kb)
        except TelegramForbiddenError:
            log.warning("notify_auto: %s заблокировал бота", recv_id)
        except Exception as e:
            log.warning("notify_auto: не удалось уведомить %s: %s", recv_id, e)


_AUTOPANEL_SECTIONS = {
    "mute":    "🔇 Замьюченные",
    "ban":     "⛔ Забаненные",
    "pending": "⏳ Авто-мьют (ждут решения)",
    "autoban": "🚫 Авто-бан (журнал)",
}


def _autopanel_keyboard(chat_id: int, active: str) -> InlineKeyboardMarkup:
    row = []
    for key, label in _AUTOPANEL_SECTIONS.items():
        text = f"• {label}" if key == active else label
        row.append(InlineKeyboardButton(text=text, callback_data=f"autopanel:{key}:{chat_id}"))
    # 2 кнопки в ряд, чтобы влезало на любом экране
    kb_rows = [row[i:i + 2] for i in range(0, len(row), 2)]
    return InlineKeyboardMarkup(inline_keyboard=kb_rows)


def _render_autopanel_section(chat_id: int, section: str) -> str:
    title = _AUTOPANEL_SECTIONS.get(section, section)
    lines = [f"🤖 <b>Авто-действия бота</b>\n\n<b>{title}</b>\n"]

    if section == "mute":
        ids = sorted(st.muted_users.get(chat_id, set()))
        if not ids:
            lines.append("✅ Замьюченных нет.")
        else:
            lines.append(f"Всего: <b>{len(ids)}</b> (показано до 20)\n")
        for uid in ids[:20]:
            meta  = st.mute_meta.get(chat_id, {}).get(uid, {})
            rsn   = esc(meta.get("reason", "—"))
            ts    = meta.get("ts", 0)
            ago   = _fmt_duration(int(time.time() - ts)) if ts else "?"
            until = meta.get("until")
            dur   = f"до {datetime.fromtimestamp(until, tz=timezone.utc).strftime('%d.%m %H:%M')} UTC" if until else "навсегда"
            lines.append(
                f"🔇 {mention_by_id(uid, str(uid))} <code>{uid}</code>\n"
                f"   📝 {rsn} · {dur} · {ago} назад"
            )
        if len(ids) > 20:
            lines.append(f"\n… и ещё {len(ids) - 20}")

    elif section == "ban":
        ids = sorted(st.banned_users.get(chat_id, set()))
        if not ids:
            lines.append("✅ Забаненных нет.")
        else:
            lines.append(f"Всего: <b>{len(ids)}</b> (показано до 20)\n")
        for uid in ids[:20]:
            meta = st.ban_meta.get(chat_id, {}).get(uid, {})
            rsn  = esc(meta.get("reason", "—"))
            ts   = meta.get("ts", 0)
            ago  = _fmt_duration(int(time.time() - ts)) if ts else "?"
            lines.append(
                f"⛔ {mention_by_id(uid, str(uid))} <code>{uid}</code>\n"
                f"   📝 {rsn} · {ago} назад"
            )
        if len(ids) > 20:
            lines.append(f"\n… и ещё {len(ids) - 20}")

    elif section == "pending":
        items = [v for v in st.pending_auto_mutes.values() if v["chat_id"] == chat_id]
        items.sort(key=lambda v: v["ts"], reverse=True)
        if not items:
            lines.append("✅ Нет авто-действий, ожидающих решения.")
        for it in items[:20]:
            ago = _fmt_duration(max(0, int(time.time() - it["ts"])))
            lines.append(
                f"⏳ {mention_by_id(it['target_id'], it['target_name'])} — "
                f"<code>{it['target_id']}</code>\n"
                f"📝 {esc(it['reason'])}\n⏱ {ago} назад\n"
            )
        if len(items) > 20:
            lines.append(f"… и ещё {len(items) - 20}")

    elif section == "autoban":
        items = [v for v in st.auto_ban_log if v["chat_id"] == chat_id]
        items.sort(key=lambda v: v["ts"], reverse=True)
        if not items:
            lines.append("✅ Пока пусто.")
        for it in items[:20]:
            ago = _fmt_duration(max(0, int(time.time() - it["ts"])))
            lines.append(
                f"🚫 {mention_by_id(it['uid'], it['name'])} — <code>{it['uid']}</code>\n"
                f"📝 {esc(it['reason'])} · {ago} назад\n"
            )
        if len(items) > 20:
            lines.append(f"… и ещё {len(items) - 20}")

    return "\n".join(lines)


def _mute_list_keyboard(chat_id: int) -> InlineKeyboardMarkup:
    """Клавиатура для раздела «Замьюченные»: таб-кнопки + кнопка размута под каждым."""
    kb_rows = _autopanel_keyboard(chat_id, "mute").inline_keyboard[:]
    ids = sorted(st.muted_users.get(chat_id, set()))
    for uid in ids[:20]:
        kb_rows.append([
            InlineKeyboardButton(
                text=f"🔊 Размутить {uid}",
                callback_data=f"ap_do:unmute:{chat_id}:{uid}",
            ),
        ])
    return InlineKeyboardMarkup(inline_keyboard=kb_rows)


def _ban_list_keyboard(chat_id: int) -> InlineKeyboardMarkup:
    """Клавиатура для раздела «Забаненные»: таб-кнопки + кнопка разбана под каждым."""
    kb_rows = _autopanel_keyboard(chat_id, "ban").inline_keyboard[:]
    ids = sorted(st.banned_users.get(chat_id, set()))
    for uid in ids[:20]:
        kb_rows.append([
            InlineKeyboardButton(
                text=f"✅ Разбанить {uid}",
                callback_data=f"ap_do:unban:{chat_id}:{uid}",
            ),
        ])
    return InlineKeyboardMarkup(inline_keyboard=kb_rows)


async def _perform_unmute_action(chat_id: int, target_id: int, notif_id: str, actor_uid: int) -> None:
    msg_hash = st.notif_hash.pop(notif_id, "")
    st.pending_auto_mutes.pop(notif_id, None)
    try:
        await unmute_user(bot, chat_id, target_id)
    except Exception:
        pass
    try:
        await bot.unban_chat_member(chat_id, target_id, only_if_banned=True)
        st.banned_users[chat_id].discard(target_id)
    except Exception:
        pass
    await allow_twin_user(chat_id, target_id, actor_uid)
    # Прощаем конкретное сообщение — бот не будет мьютить за него снова,
    # но за ДРУГОЙ похожий (совпадающий с чужим) текст замьютит заново.
    if msg_hash:
        st.hash_pardons.add((chat_id, target_id, msg_hash))
    await db_log("SA_UNMUTE", actor_uid, target_id, chat_id, "Размут/разбан")


def _perform_keep_action(notif_id: str) -> None:
    st.pending_auto_mutes.pop(notif_id, None)
    st.notif_hash.pop(notif_id, None)


def _pending_items_keyboard(chat_id: int) -> InlineKeyboardMarkup:
    """Клавиатура раздела «Ожидают решения»: переключатели разделов +
    по паре кнопок «Размутить/Разбанить» / «Оставить» под каждым авто-действием."""
    kb_rows = _autopanel_keyboard(chat_id, "pending").inline_keyboard[:]
    items = [
        (nid, v) for nid, v in st.pending_auto_mutes.items()
        if v["chat_id"] == chat_id
    ]
    items.sort(key=lambda x: x[1]["ts"], reverse=True)
    for notif_id, it in items[:20]:
        cb_base = f"{notif_id}:{chat_id}:{it['target_id']}"
        kb_rows.append([
            InlineKeyboardButton(text="🔊 Размутить/Разбанить", callback_data=f"ap_unmute:{cb_base}"),
            InlineKeyboardButton(text="🔇 Оставить", callback_data=f"ap_keep:{cb_base}"),
        ])
    return InlineKeyboardMarkup(inline_keyboard=kb_rows)



bot  = Bot(token=BOT_TOKEN, parse_mode=ParseMode.HTML)
dp   = Dispatcher()
r    = Router()
dp.include_router(r)


# ─────────────────────────────────────────────────────────
# CALLBACKS
# ─────────────────────────────────────────────────────────

@r.callback_query(F.data.startswith("autopanel:"))
async def cb_autopanel(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    if uid not in SUPER_ADMINS and uid not in st.mods and not await is_chat_admin(bot, cq.message.chat.id, uid):
        return await cq.answer("⛔ Только для админов и модераторов.", show_alert=True)

    _, section, chat_id_s = cq.data.split(":")
    chat_id = int(chat_id_s)
    if section == "pending":
        kb = _pending_items_keyboard(chat_id)
    elif section == "mute":
        kb = _mute_list_keyboard(chat_id)
    elif section == "ban":
        kb = _ban_list_keyboard(chat_id)
    else:
        kb = _autopanel_keyboard(chat_id, section)
    try:
        await cq.message.edit_text(
            _render_autopanel_section(chat_id, section),
            reply_markup=kb,
        )
    except TelegramBadRequest:
        pass  # текст не поменялся (уже на этом разделе) — не ошибка
    except Exception:
        pass
    await cq.answer()


@r.callback_query(F.data.startswith("sa_unmute:"))
async def cb_sa_unmute(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    if uid not in SUPER_ADMINS and uid not in st.mods:
        return await cq.answer("⛔ Только для супер-админов и модераторов.", show_alert=True)

    parts = cq.data.split(":")  # sa_unmute:notif_id:chat_id:target_id
    notif_id  = parts[1]
    chat_id   = int(parts[2])
    target_id = int(parts[3])

    if notif_id in st.action_taken:
        who = st.action_taken[notif_id]
        return await cq.answer(f"⚠️ Уже обработано: {who}", show_alert=True)
    actor_name = cq.from_user.first_name or str(uid)
    st.action_taken[notif_id] = actor_name

    await _perform_unmute_action(chat_id, target_id, notif_id, uid)

    try:
        await cq.message.edit_text(
            cq.message.text + f"\n\n✅ <b>Размьючен/разбанен</b> — {esc(actor_name)}",
            reply_markup=None,
        )
    except Exception:
        pass
    await cq.answer("✅ Готово!")


@r.callback_query(F.data.startswith("sa_keep:"))
async def cb_sa_keep(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    if uid not in SUPER_ADMINS and uid not in st.mods:
        return await cq.answer("⛔ Только для супер-админов и модераторов.", show_alert=True)

    parts    = cq.data.split(":")  # sa_keep:notif_id:chat_id:target_id
    notif_id = parts[1]

    if notif_id in st.action_taken:
        who = st.action_taken[notif_id]
        return await cq.answer(f"⚠️ Уже обработано: {who}", show_alert=True)
    actor_name = cq.from_user.first_name or str(uid)
    st.action_taken[notif_id] = actor_name
    _perform_keep_action(notif_id)

    try:
        await cq.message.edit_text(
            cq.message.text + f"\n\n🔇 <b>Оставлен</b> — {esc(actor_name)}",
            reply_markup=None,
        )
    except Exception:
        pass
    await cq.answer("🔇 Оставлено.")


@r.callback_query(F.data.startswith("ap_unmute:"))
async def cb_ap_unmute(cq: CallbackQuery) -> None:
    """Кнопка «Размутить/Разбанить» прямо из панели «Авто-действия» → «Ожидают решения»."""
    uid = cq.from_user.id
    if uid not in SUPER_ADMINS and uid not in st.mods and not await is_chat_admin(bot, cq.message.chat.id, uid):
        return await cq.answer("⛔ Только для админов и модераторов.", show_alert=True)

    parts = cq.data.split(":")  # ap_unmute:notif_id:chat_id:target_id
    notif_id  = parts[1]
    chat_id   = int(parts[2])
    target_id = int(parts[3])

    if notif_id in st.action_taken:
        who = st.action_taken[notif_id]
        return await cq.answer(f"⚠️ Уже обработано: {who}", show_alert=True)
    actor_name = cq.from_user.first_name or str(uid)
    st.action_taken[notif_id] = actor_name

    await _perform_unmute_action(chat_id, target_id, notif_id, uid)

    try:
        await cq.message.edit_text(
            _render_autopanel_section(chat_id, "pending"),
            reply_markup=_pending_items_keyboard(chat_id),
        )
    except TelegramBadRequest:
        pass
    except Exception:
        pass
    await cq.answer("✅ Готово!")


@r.callback_query(F.data.startswith("ap_keep:"))
async def cb_ap_keep(cq: CallbackQuery) -> None:
    """Кнопка «Оставить» прямо из панели «Авто-действия» → «Ожидают решения»."""
    uid = cq.from_user.id
    if uid not in SUPER_ADMINS and uid not in st.mods and not await is_chat_admin(bot, cq.message.chat.id, uid):
        return await cq.answer("⛔ Только для админов и модераторов.", show_alert=True)

    parts    = cq.data.split(":")  # ap_keep:notif_id:chat_id:target_id
    notif_id = parts[1]
    chat_id  = int(parts[2])

    if notif_id in st.action_taken:
        who = st.action_taken[notif_id]
        return await cq.answer(f"⚠️ Уже обработано: {who}", show_alert=True)
    actor_name = cq.from_user.first_name or str(uid)
    st.action_taken[notif_id] = actor_name
    _perform_keep_action(notif_id)

    try:
        await cq.message.edit_text(
            _render_autopanel_section(chat_id, "pending"),
            reply_markup=_pending_items_keyboard(chat_id),
        )
    except TelegramBadRequest:
        pass
    except Exception:
        pass
    await cq.answer("🔇 Оставлено.")


@r.callback_query(F.data.startswith("ap_do:"))
async def cb_ap_do(cq: CallbackQuery) -> None:
    """Прямые кнопки «Размутить» / «Разбанить» из списков мьютов и банов."""
    uid = cq.from_user.id
    if uid not in SUPER_ADMINS and uid not in st.mods and not await is_chat_admin(bot, cq.message.chat.id, uid):
        return await cq.answer("⛔ Только для админов и модераторов.", show_alert=True)

    # ap_do:unmute:chat_id:target_id  OR  ap_do:unban:chat_id:target_id
    parts     = cq.data.split(":")
    action    = parts[1]          # "unmute" | "unban"
    chat_id   = int(parts[2])
    target_id = int(parts[3])
    actor_name = cq.from_user.first_name or str(uid)

    try:
        if action == "unmute":
            await unmute_user(bot, chat_id, target_id)
            await allow_twin_user(chat_id, target_id, uid)
            await db_log("UNMUTE", uid, target_id, chat_id, f"Панель авто-действий ({actor_name})")
            await cq.answer(f"✅ {target_id} размьючен!")
            # Обновляем панель
            try:
                await cq.message.edit_text(
                    _render_autopanel_section(chat_id, "mute"),
                    reply_markup=_mute_list_keyboard(chat_id),
                )
            except TelegramBadRequest:
                pass
        elif action == "unban":
            await bot.unban_chat_member(chat_id, target_id)
            st.banned_users[chat_id].discard(target_id)
            st.ban_meta[chat_id].pop(target_id, None)
            await allow_twin_user(chat_id, target_id, uid)
            await db_log("UNBAN", uid, target_id, chat_id, f"Панель авто-действий ({actor_name})")
            await cq.answer(f"✅ {target_id} разбанен!")
            try:
                await cq.message.edit_text(
                    _render_autopanel_section(chat_id, "ban"),
                    reply_markup=_ban_list_keyboard(chat_id),
                )
            except TelegramBadRequest:
                pass
        else:
            await cq.answer("❌ Неизвестное действие.", show_alert=True)
    except TelegramForbiddenError:
        await cq.answer("⛔ Нет прав в чате.", show_alert=True)
    except TelegramBadRequest as e:
        await cq.answer(f"⚠️ {e}", show_alert=True)
    except Exception as e:
        log.warning("cb_ap_do error: %s", e)
        await cq.answer("❌ Ошибка.", show_alert=True)


@r.callback_query(F.data.startswith("mat_silent:"))
async def cb_mat_silent(cq: CallbackQuery) -> None:
    """«🔇 Удалять впредь» — бот молча удаляет все следующие матерные от юзера без форварда."""
    uid = cq.from_user.id
    parts      = cq.data.split(":")  # mat_silent:notif_id:chat_id:target_uid
    notif_id   = parts[1]
    chat_id    = int(parts[2])
    target_uid = int(parts[3])

    if uid not in SUPER_ADMINS and uid not in st.mods and not await is_chat_admin(bot, chat_id, uid):
        return await cq.answer("⛔ Только для модераторов.", show_alert=True)

    actor = cq.from_user.first_name or str(uid)
    st.mat_silent_users.add((chat_id, target_uid))
    await db_log("MAT_SILENT_ON", uid, target_uid, chat_id, f"Тихий режим включён модератором {actor}")
    await cq.answer("🔇 Готово. Все следующие матерные от этого юзера будут удаляться молча.")

    result = (
        f"🔇 <b>Удалять впредь</b> — решение {esc(actor)}\n"
        f"👤 <code>{target_uid}</code>\n"
        f"<i>Бот будет молча удалять все матерные от этого пользователя.</i>"
    )
    await _mat_close_notifs(bot, notif_id, result)


@r.callback_query(F.data.startswith("mat_ign:"))
async def cb_mat_ignore(cq: CallbackQuery) -> None:
    """«👌 Не реагировать» — пропустить именно этот форвард, следующее матерное снова пришлёт."""
    uid = cq.from_user.id
    parts      = cq.data.split(":")  # mat_ign:notif_id:chat_id:target_uid
    notif_id   = parts[1]
    chat_id    = int(parts[2])
    target_uid = int(parts[3])

    if uid not in SUPER_ADMINS and uid not in st.mods and not await is_chat_admin(bot, chat_id, uid):
        return await cq.answer("⛔ Только для модераторов.", show_alert=True)

    actor = cq.from_user.first_name or str(uid)
    # Добавляем хэш — бот игнорирует точно такой же текст от этого юзера впредь
    data = st.mat_pending.get(notif_id, {})
    msg_hash = data.get("msg_hash", "")
    if msg_hash:
        st.hash_pardons.add((chat_id, target_uid, msg_hash))
    await db_log("MAT_IGNORE", uid, target_uid, chat_id, f"Проигнорировано модератором {actor}")
    await cq.answer("👌 Окей. Следующее матерное от этого юзера снова пришлёт форвард.")

    result = (
        f"👌 <b>Не реагировать</b> — решение {esc(actor)}\n"
        f"👤 <code>{target_uid}</code>\n"
        f"<i>Следующее матерное от этого пользователя — снова форвард.</i>"
    )
    await _mat_close_notifs(bot, notif_id, result)


@r.callback_query(F.data.startswith("doxx_ban:"))
async def cb_doxx_ban(cq: CallbackQuery) -> None:
    """Подтверждение: бан за угрозу докса/слива данных."""
    uid = cq.from_user.id
    parts      = cq.data.split(":")  # doxx_ban:notif_id:chat_id:target_uid
    notif_id   = parts[1]
    chat_id    = int(parts[2])
    target_uid = int(parts[3])

    if uid not in SUPER_ADMINS and uid not in st.mods and not await is_chat_admin(bot, chat_id, uid):
        return await cq.answer("⛔ Только для модераторов.", show_alert=True)
    if notif_id not in st.doxx_pending:
        return await cq.answer("⚠️ Уже обработано другим модератором.", show_alert=True)

    actor = cq.from_user.first_name or str(uid)
    try:
        await bot.ban_chat_member(chat_id, target_uid)
    except Exception:
        pass
    st.banned_users[chat_id].add(target_uid)
    st.muted_users[chat_id].discard(target_uid)
    st.ban_meta[chat_id][target_uid] = {
        "reason": "Докс/угроза слива данных (подтверждено)", "ts": time.time(), "mod_id": uid,
    }
    remember_recent_punishment(chat_id, target_uid, "ban")
    await db_log("BAN_PERM", uid, target_uid, chat_id, f"Докс/угрозы — подтверждено ({actor})")
    await cq.answer("🚫 Пользователь забанен.")

    result = (
        f"🚫 <b>Забанен</b> — решение {esc(actor)}\n"
        f"👤 <code>{target_uid}</code>\n"
        f"<i>Причина: угроза доксом/сливом данных.</i>"
    )
    await _doxx_close_notifs(bot, notif_id, result)


@r.callback_query(F.data.startswith("doxx_unmute:"))
async def cb_doxx_unmute(cq: CallbackQuery) -> None:
    """Ложное срабатывание: снять мут, восстановить доступ."""
    uid = cq.from_user.id
    parts      = cq.data.split(":")  # doxx_unmute:notif_id:chat_id:target_uid
    notif_id   = parts[1]
    chat_id    = int(parts[2])
    target_uid = int(parts[3])

    if uid not in SUPER_ADMINS and uid not in st.mods and not await is_chat_admin(bot, chat_id, uid):
        return await cq.answer("⛔ Только для модераторов.", show_alert=True)
    if notif_id not in st.doxx_pending:
        return await cq.answer("⚠️ Уже обработано другим модератором.", show_alert=True)

    actor = cq.from_user.first_name or str(uid)
    msg_hash = st.notif_hash.pop(notif_id, "")
    try:
        await unmute_user(bot, chat_id, target_uid)
    except Exception:
        pass
    await allow_twin_user(chat_id, target_uid, uid)
    if msg_hash:
        st.hash_pardons.add((chat_id, target_uid, msg_hash))
    await db_log("SA_UNMUTE", uid, target_uid, chat_id, f"Докс/угрозы — ложное срабатывание ({actor})")
    await cq.answer("🔊 Размучен.")

    result = (
        f"🔊 <b>Размучен (ложное срабатывание)</b> — решение {esc(actor)}\n"
        f"👤 <code>{target_uid}</code>"
    )
    await _doxx_close_notifs(bot, notif_id, result)


@r.callback_query(F.data.startswith("deal_accept:"))
async def cb_deal_accept(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    if uid not in st.garants and uid not in SUPER_ADMINS:
        return await cq.answer("⛔ Только для гарантов.", show_alert=True)

    parts   = cq.data.split(":", 2)
    deal_id = parts[1]
    chat_id = int(parts[2])

    if deal_id in st.accepted_deals:
        already_uid = st.accepted_deals[deal_id]
        status = st.deal_status.get(deal_id, "")
        if already_uid == uid and status not in {"clarified", "clarification_requested"}:
            return await cq.answer("Вы уже приняли эту сделку!", show_alert=True)
        if already_uid != uid and status not in {"clarified", "clarification_requested"}:
            return await cq.answer("❌ Эту сделку уже принял другой гарант.", show_alert=True)

    st.accepted_deals[deal_id] = uid
    st.garant_pending_deal[uid] = deal_id
    st.deal_status[deal_id] = "accepted_waiting_link"
    gname  = esc(cq.from_user.first_name or "Гарант")
    garant_mention = f'<a href="tg://user?id={uid}">{gname}</a>'

    try:
        await cq.message.edit_text(
            cq.message.text + f"\n\n✅ <b>Вы приняли эту сделку!</b>",
            reply_markup=None,
        )
    except Exception:
        pass

    await cq.answer("✅ Вы приняли сделку!")
    try:
        await bot.send_message(uid, "🔗 <b>Вы приняли сделку</b>\n\nПришлите в ЛС одну ссылку на гарант-чат для участников сделки.\nЕсли хотите, можете сначала написать <code>готов</code> — я повторно запрошу ссылку.")
    except Exception:
        pass

    garant_ids, garant_usernames = await get_cached_garant_data()

    for g_uid in garant_ids:
        if g_uid == uid:
            continue
        try:
            await bot.send_message(
                g_uid,
                f"ℹ️ Эту сделку уже принял гарант {garant_mention}.\n"
                f"Дополнительных действий от вас не требуется."
            )
        except Exception:
            pass

    body = st.deal_participants.get(deal_id, "")
    participant_mentions = await get_participant_mentions(bot, chat_id, body, garant_usernames)

    if participant_mentions:
        if len(participant_mentions) == 1:
            participants_str = participant_mentions[0]
        elif len(participant_mentions) == 2:
            participants_str = f"{participant_mentions[0]} и {participant_mentions[1]}"
        else:
            participants_str = ", ".join(participant_mentions[:-1]) + f" и {participant_mentions[-1]}"
    else:
        participants_str = None

    chat_text = (
        f"✅ {garant_mention} готов провести сделку!\n\n"
        f"{'👥 ' + participants_str + chr(10) + chr(10) if participants_str else ''}"
        f"💬 Гарант принял сделку. Ожидайте ссылку на чат сделок в ЛС бота. 🤝"
    )

    try:
        await bot.send_message(chat_id, chat_text)
    except Exception as e:
        log.warning("Не удалось отправить в чат о принятии сделки: %s", e)

    all_raw = _RE_MENTION.findall(body)
    for m_str in dict.fromkeys(all_raw):
        uname_clean = m_str.lstrip("@").lower()
        if uname_clean in garant_usernames:
            continue
        user = await resolve_user(bot, chat_id, uname_clean)
        if not user:
            continue
        try:
            await bot.send_message(
                user.id,
                f"🤝 {garant_mention} принял вашу сделку.\n\n"
                f"⏳ Одидайте ссылку на чат сделок, бот пришлёт её вам в ЛС. "
                f"Если бот вам не пишет — запустите его через <code>/start</code>."
            )
        except TelegramForbiddenError:
            pass
        except Exception as e:
            log.warning("Не удалось уведомить %s: %s", uname_clean, e)


@r.callback_query(F.data.startswith("deal_clarify:"))
async def cb_deal_clarify(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    if uid not in st.garants and uid not in SUPER_ADMINS:
        return await cq.answer("⛔ Только для гарантов.", show_alert=True)
    parts = cq.data.split(":", 2)
    deal_id = parts[1]
    chat_id = int(parts[2])
    if deal_id in st.accepted_deals and st.accepted_deals[deal_id] != uid:
        return await cq.answer("❌ Эту сделку уже принял другой гарант.", show_alert=True)
    st.accepted_deals[deal_id] = uid
    st.garant_pending_deal[uid] = deal_id
    st.deal_status[deal_id] = "clarification_requested"
    st.deal_clarification_target[deal_id] = uid
    try:
        await cq.message.edit_text(
            cq.message.text + "\n\n📝 <b>Гарант запросил уточнение</b>",
            reply_markup=None,
        )
    except Exception:
        pass

    body = st.deal_participants.get(deal_id, "")
    actor_name = esc(cq.from_user.first_name or "Гарант")
    try:
        await bot.send_message(
            chat_id,
            f"📝 <b>Нужно уточнение</b>\n\n"
            f"👤 Инициатор, пожалуйста, уточните детали сделки сообщением <b>ответом на исходный вызов</b>.\n"
            f"📌 Что желательно уточнить:\n"
            f"• точную сумму\n"
            f"• предмет сделки\n"
            f"• важные условия\n\n"
            f"🤝 Запросил: <b>{actor_name}</b>\n"
            f"🧾 Текущий запрос:\n<blockquote>{esc(body)}</blockquote>"
        )
    except Exception:
        pass
    try:
        await bot.send_message(uid, "📝 Уточнение запрошено в чате. После ответа инициатора вы сможете снова принять сделку кнопкой.")
    except Exception:
        pass
    await cq.answer("Запрос на уточнение отправлен.")


@r.callback_query(F.data.startswith("deal_decline:"))
async def cb_deal_decline(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    if uid not in st.garants and uid not in SUPER_ADMINS:
        return await cq.answer("⛔ Только для гарантов.", show_alert=True)
    parts = cq.data.split(":", 2)
    deal_id = parts[1]
    chat_id = int(parts[2])
    st.deal_status[deal_id] = "declined"
    try:
        await cq.message.edit_text(
            cq.message.text + f"\n\n❌ <b>Сделка отклонена</b> — {mention(cq.from_user)}",
            reply_markup=None,
        )
    except Exception:
        pass
    try:
        await bot.send_message(chat_id, "❌ Гарант отклонил запрос. При необходимости оформите новый вызов с более точными деталями сделки.")
    except Exception:
        pass
    await cq.answer("Сделка отклонена.")


# ─────────────────────────────────────────────────────────
# /start
# ─────────────────────────────────────────────────────────

def user_start_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🧾 Подать апелляцию", callback_data="menu_appeal")],
        [InlineKeyboardButton(text="👑 Владельцы чата", callback_data="menu_owners")],
    ])


def appeal_prompt_text() -> str:
    return (
        "🧾 <b>Апелляция</b>\n\n"
        "Опишите ситуацию одним сообщением: кратко укажите причину и контекст.\n"
        "Просто отправьте текст следующим сообщением сюда, в ЛС.\n"
        f"⚠️ Лимит: до <b>{APPEAL_MAX_LEN}</b> символов.\n\n"
        "Решение будет принято администрацией и в дальнейшем сообщено вам."
    )


@r.message(Command("start"))
async def cmd_start(msg: Message) -> None:
    uid = msg.from_user.id

    me = await bot.get_me()
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(
            text="➕ Добавить в чат",
            url=(
                f"https://t.me/{me.username}?startgroup=true"
                "&admin=restrict_members+ban_users+delete_messages+pin_messages"
            ),
        )],
        [
            InlineKeyboardButton(text="📜 Правила",  callback_data="show_rules"),
            InlineKeyboardButton(text="🛠 Команды", callback_data="show_help"),
        ],
        [
            InlineKeyboardButton(text="🧾 Апелляция", callback_data="menu_appeal"),
            InlineKeyboardButton(text="👑 Владельцы", callback_data="menu_owners"),
        ],
        [
            InlineKeyboardButton(text="🤖 Авто-действия", callback_data=f"autopanel:mute:{msg.chat.id}"),
            InlineKeyboardButton(text="⚙️ Настройки", callback_data="menu_settings"),
        ],
        [
            InlineKeyboardButton(text="📋 Правила и наказания", callback_data="menu_rules_panel"),
        ],
    ])
    if msg.chat.type == "private":
        if uid in SUPER_ADMINS:
            await msg.answer(ADMIN_START_TEXT, reply_markup=kb)
        else:
            await msg.answer(
                "🤖 <b>Cz Chat Manager</b>\n"
                "Чат: <b>@chatnft2</b>\n\n"
                "Моя задача: помогаю модерировать Cz Garant Chat.\n"
                "🧾 Апелляция: нажмите кнопку «Подать апелляцию» ниже",
                reply_markup=user_start_menu(),
            )
    else:
        await msg.answer(ADMIN_START_TEXT, reply_markup=kb)


@r.callback_query(F.data == "menu_appeal")
async def cb_menu_appeal(cq: CallbackQuery) -> None:
    st.awaiting_appeal.add(cq.from_user.id)
    await cq.message.answer(appeal_prompt_text())
    await cq.answer()


@r.callback_query(F.data == "menu_owners")
async def cb_menu_owners(cq: CallbackQuery) -> None:
    await cq.message.answer(
        "👑 <b>Владельцы чата @chatnft2:</b>\n"
        "• @Timmy_Falcon\n"
        "• @mrtley"
    )
    await cq.answer()


# ─────────────────────────────────────────────────────────
# ПАНЕЛЬ НАСТРОЕК ЧАТА
# ─────────────────────────────────────────────────────────

def _settings_keyboard(chat_id: int, settings: dict[str, bool]) -> InlineKeyboardMarkup:
    rows = []
    for key, label in _SETTINGS_LABELS.items():
        val = settings.get(key, True)
        toggle = "✅" if val else "❌"
        rows.append([InlineKeyboardButton(
            text=f"{toggle} {label}",
            callback_data=f"cfg_toggle:{chat_id}:{key}",
        )])
    rows.append([InlineKeyboardButton(text="◀️ Назад", callback_data="cfg_back")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def _settings_text(chat_id: int, settings: dict[str, bool]) -> str:
    lines = [f"⚙️ <b>Настройки чата</b> <code>{chat_id}</code>\n"]
    for key, label in _SETTINGS_LABELS.items():
        val = settings.get(key, True)
        lines.append(f"{'✅' if val else '❌'} {label}")
    lines.append("\n<i>Нажмите кнопку, чтобы включить/выключить.</i>")
    return "\n".join(lines)


@r.callback_query(F.data == "menu_settings")
async def cb_menu_settings(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    if uid not in SUPER_ADMINS and uid not in st.mods:
        return await cq.answer("⛔ Только для супер-админов и модераторов.", show_alert=True)
    chat_id = MAIN_CHAT_ID
    settings = await db_get_settings(chat_id)
    try:
        await cq.message.edit_text(
            _settings_text(chat_id, settings),
            reply_markup=_settings_keyboard(chat_id, settings),
        )
    except Exception:
        await cq.message.answer(
            _settings_text(chat_id, settings),
            reply_markup=_settings_keyboard(chat_id, settings),
        )
    await cq.answer()


@r.callback_query(F.data.startswith("cfg_toggle:"))
async def cb_cfg_toggle(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    if uid not in SUPER_ADMINS and uid not in st.mods:
        return await cq.answer("⛔ Только для супер-админов и модераторов.", show_alert=True)
    _, chat_id_s, key = cq.data.split(":", 2)
    chat_id = int(chat_id_s)
    if key not in _SETTINGS_DEFAULTS:
        return await cq.answer("❌ Неизвестная настройка.", show_alert=True)
    settings = await db_get_settings(chat_id)
    new_val = not settings.get(key, True)
    await db_set_setting(chat_id, key, new_val)
    settings[key] = new_val
    label = _SETTINGS_LABELS[key]
    state_str = "включено ✅" if new_val else "выключено ❌"
    try:
        await cq.message.edit_text(
            _settings_text(chat_id, settings),
            reply_markup=_settings_keyboard(chat_id, settings),
        )
    except Exception:
        pass
    await cq.answer(f"{label}: {state_str}")


# ─────────────────────────────────────────────────────────
# ПАНЕЛЬ ПРАВИЛ И НАКАЗАНИЙ
# ─────────────────────────────────────────────────────────

_RULE_ACTION_LABELS = {"mute": "🔇 Мут", "ban": "🚫 Бан"}

def _rules_panel_text() -> str:
    if not st.rules_cache:
        return "📋 <b>Правила и наказания</b>\n\n<i>Нет правил.</i>"
    lines = ["📋 <b>Правила и наказания</b>\n<i>Нажмите правило, чтобы изменить наказание</i>\n"]
    for num in sorted(st.rules_cache):
        r = st.rules_cache[num]
        action_str = _RULE_ACTION_LABELS.get(r["action"], r["action"])
        lines.append(f"<b>{num}.</b> {r['description']} — {action_str} <b>{r['duration_label']}</b>")
    return "\n".join(lines)


def _rules_panel_keyboard() -> InlineKeyboardMarkup:
    rows = []
    for num in sorted(st.rules_cache):
        r = st.rules_cache[num]
        rows.append([InlineKeyboardButton(
            text=f"✏️ {num}. {r['description'][:30]}",
            callback_data=f"rule_edit:{num}",
        )])
    rows.append([InlineKeyboardButton(text="◀️ Назад", callback_data="cfg_back")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def _rule_edit_keyboard(rule_num: int) -> InlineKeyboardMarkup:
    r = st.rules_cache.get(rule_num, {})
    cur_action = r.get("action", "mute")
    rows = [
        [
            InlineKeyboardButton(
                text=f"{'✅' if cur_action == 'mute' else '⬜'} Мут",
                callback_data=f"rule_set:{rule_num}:action:mute",
            ),
            InlineKeyboardButton(
                text=f"{'✅' if cur_action == 'ban' else '⬜'} Бан",
                callback_data=f"rule_set:{rule_num}:action:ban",
            ),
        ],
    ]
    durations = [
        (3600,      "1 час"),
        (3*3600,    "3 часа"),
        (86400,     "1 день"),
        (3*86400,   "3 дня"),
        (7*86400,   "1 неделю"),
        (30*86400,  "30 дней"),
        (0,         "навсегда"),
    ]
    cur_dur = r.get("duration", 0)
    dur_row = []
    for secs, label in durations:
        mark = "✅" if secs == cur_dur else "⬜"
        dur_row.append(InlineKeyboardButton(
            text=f"{mark} {label}",
            callback_data=f"rule_set:{rule_num}:dur:{secs}:{label}",
        ))
        if len(dur_row) == 3:
            rows.append(dur_row)
            dur_row = []
    if dur_row:
        rows.append(dur_row)
    # Кнопка "Своё время" — позволяет ввести произвольное значение текстом
    rows.append([
        InlineKeyboardButton(text="✏️ Своё время…", callback_data=f"rule_custom_time:{rule_num}"),
    ])
    rows.append([InlineKeyboardButton(text="◀️ К списку правил", callback_data="menu_rules_panel")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def _rule_edit_text(rule_num: int) -> str:
    r = st.rules_cache.get(rule_num)
    if not r:
        return "❌ Правило не найдено."
    action_str = _RULE_ACTION_LABELS.get(r["action"], r["action"])
    return (
        f"✏️ <b>Редактирование правила {rule_num}</b>\n\n"
        f"📌 <b>{r['description']}</b>\n\n"
        f"Текущее наказание: {action_str} <b>{r['duration_label']}</b>\n\n"
        f"Выберите действие и длительность:"
    )


@r.callback_query(F.data.startswith("rule_custom_time:"))
async def cb_rule_custom_time(cq: CallbackQuery) -> None:
    """Нажата кнопка «Своё время» — просим ввести время текстом в ЛС."""
    uid = cq.from_user.id
    if uid not in SUPER_ADMINS and uid not in st.mods:
        return await cq.answer("⛔ Только для супер-админов и модераторов.", show_alert=True)
    rule_num = int(cq.data.split(":")[1])
    if rule_num not in st.rules_cache:
        return await cq.answer("❌ Правило не найдено.", show_alert=True)
    # Запоминаем что ждём ввод от этого юзера
    st.awaiting_custom_time[uid] = {"rule_num": rule_num, "msg_id": cq.message.message_id}
    await cq.answer("Введите время в следующем сообщении 👇", show_alert=False)
    await cq.message.reply(
        f"⏱ <b>Введите своё время для правила {rule_num}</b>\n\n"
        "Примеры: <code>2ч 30мин</code>, <code>5 дней</code>, <code>1 неделя</code>, "
        "<code>3 часа 20 минут</code>, <code>45мин</code>, <code>навсегда</code>\n\n"
        "Или отправьте <code>отмена</code> чтобы отменить."
    )


@r.message(F.chat.type == "private", F.func(lambda m: m.from_user.id in st.awaiting_custom_time), F.text)
async def handle_custom_time_input(msg: Message) -> None:
    """Получаем произвольное время для правила, введённое текстом в ЛС."""
    uid  = msg.from_user.id
    data = st.awaiting_custom_time.pop(uid, None)
    if not data:
        return
    text = (msg.text or "").strip()
    if text.lower() in ("отмена", "cancel", "/cancel"):
        return await msg.reply("❌ Отменено.")
    rule_num = data["rule_num"]
    if rule_num not in st.rules_cache:
        return await msg.reply("❌ Правило не найдено.")
    secs, label = parse_time(text)
    if secs is None:
        # Возвращаем в очередь — даём ещё попытку
        st.awaiting_custom_time[uid] = data
        return await msg.reply(
            f"❌ Не распознал время: <code>{esc(text[:40])}</code>\n\n"
            "Попробуйте ещё раз. Примеры: <code>2ч 30мин</code>, <code>5 дней</code>, "
            "<code>45мин</code>, <code>навсегда</code>\n"
            "Или отправьте <code>отмена</code>."
        )
    # _FOREVER_SECS=-1 → 0 секунд в БД (навсегда)
    db_secs = 0 if secs == _FOREVER_SECS else secs
    r = st.rules_cache[rule_num]
    r["duration"]       = db_secs
    r["duration_label"] = label
    async with st.pool.acquire() as c:
        await c.execute(
            "UPDATE rules SET duration=$1, duration_label=$2 WHERE rule_num=$3",
            db_secs, label, rule_num,
        )
    await msg.reply(
        f"✅ <b>Правило {rule_num}</b> обновлено\n"
        f"⏱ Длительность: <b>{label}</b>\n\n"
        f"📌 {esc(r['description'])}"
    )
    # Обновляем сообщение с клавиатурой если оно ещё живо
    try:
        await bot.edit_message_text(
            _rule_edit_text(rule_num),
            chat_id=msg.chat.id,
            message_id=data["msg_id"],
            reply_markup=_rule_edit_keyboard(rule_num),
        )
    except Exception:
        pass


@r.callback_query(F.data == "menu_rules_panel")
async def cb_menu_rules_panel(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    if uid not in SUPER_ADMINS and uid not in st.mods:
        return await cq.answer("⛔ Только для супер-админов и модераторов.", show_alert=True)
    try:
        await cq.message.edit_text(_rules_panel_text(), reply_markup=_rules_panel_keyboard())
    except Exception:
        await cq.message.answer(_rules_panel_text(), reply_markup=_rules_panel_keyboard())
    await cq.answer()


@r.callback_query(F.data.startswith("rule_edit:"))
async def cb_rule_edit(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    if uid not in SUPER_ADMINS and uid not in st.mods:
        return await cq.answer("⛔ Только для супер-админов и модераторов.", show_alert=True)
    rule_num = int(cq.data.split(":")[1])
    if rule_num not in st.rules_cache:
        return await cq.answer("❌ Правило не найдено.", show_alert=True)
    try:
        await cq.message.edit_text(_rule_edit_text(rule_num), reply_markup=_rule_edit_keyboard(rule_num))
    except Exception:
        pass
    await cq.answer()


@r.callback_query(F.data.startswith("rule_set:"))
async def cb_rule_set(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    if uid not in SUPER_ADMINS and uid not in st.mods:
        return await cq.answer("⛔ Только для супер-админов и модераторов.", show_alert=True)

    parts = cq.data.split(":")
    # rule_set:{rule_num}:action:{value}  OR  rule_set:{rule_num}:dur:{secs}:{label}
    rule_num = int(parts[1])
    field = parts[2]

    if rule_num not in st.rules_cache:
        return await cq.answer("❌ Правило не найдено.", show_alert=True)

    r = st.rules_cache[rule_num]

    if field == "action":
        new_action = parts[3]
        if new_action not in ("mute", "ban"):
            return await cq.answer("❌ Неверное действие.", show_alert=True)
        r["action"] = new_action
        async with st.pool.acquire() as c:
            await c.execute("UPDATE rules SET action=$1 WHERE rule_num=$2", new_action, rule_num)
        await cq.answer(f"✅ Действие изменено: {_RULE_ACTION_LABELS[new_action]}")

    elif field == "dur":
        secs = int(parts[3])
        label = parts[4]
        r["duration"] = secs
        r["duration_label"] = label
        async with st.pool.acquire() as c:
            await c.execute(
                "UPDATE rules SET duration=$1, duration_label=$2 WHERE rule_num=$3",
                secs, label, rule_num,
            )
        await cq.answer(f"✅ Длительность: {label}")

    else:
        return await cq.answer("❌ Неверный параметр.", show_alert=True)

    # Обновляем сообщение
    try:
        await cq.message.edit_text(_rule_edit_text(rule_num), reply_markup=_rule_edit_keyboard(rule_num))
    except Exception:
        pass

    # Обновляем pinned правила в чате и в ЛС (фоново)
    asyncio.create_task(_broadcast_rules_update())


async def _broadcast_rules_update() -> None:
    """Отправляет обновлённые правила в чат и всем супер-админам в ЛС."""
    new_text = build_rules_text()
    # В чат
    try:
        sent = await bot.send_message(MAIN_CHAT_ID, new_text)
        try:
            await bot.pin_chat_message(MAIN_CHAT_ID, sent.message_id, disable_notification=True)
        except Exception:
            pass
    except Exception as e:
        log.warning("_broadcast_rules_update chat failed: %s", e)
    # Супер-админам в ЛС
    for sa_id in SUPER_ADMINS:
        try:
            await bot.send_message(
                sa_id,
                f"📋 <b>Правила обновлены!</b>\n\n{new_text}"
            )
        except Exception:
            pass


@r.callback_query(F.data == "cfg_back")
async def cb_cfg_back(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    me = await bot.get_me()
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(
            text="➕ Добавить в чат",
            url=f"https://t.me/{me.username}?startgroup=true&admin=restrict_members+ban_users+delete_messages+pin_messages",
        )],
        [
            InlineKeyboardButton(text="📜 Правила",  callback_data="show_rules"),
            InlineKeyboardButton(text="🛠 Команды", callback_data="show_help"),
        ],
        [
            InlineKeyboardButton(text="🧾 Апелляция", callback_data="menu_appeal"),
            InlineKeyboardButton(text="👑 Владельцы", callback_data="menu_owners"),
        ],
        [
            InlineKeyboardButton(text="🤖 Авто-действия", callback_data=f"autopanel:mute:{MAIN_CHAT_ID}"),
            InlineKeyboardButton(text="⚙️ Настройки", callback_data="menu_settings"),
        ],
    ])
    try:
        await cq.message.edit_text(ADMIN_START_TEXT, reply_markup=kb)
    except Exception:
        pass
    await cq.answer()


@r.message(F.chat.type == "private", F.text.regexp(r"(?i)^готов$"))
async def garant_ready_private(msg: Message) -> None:
    if msg.from_user.id not in st.garants and msg.from_user.id not in SUPER_ADMINS:
        return
    deal_id = st.garant_pending_deal.get(msg.from_user.id)
    if not deal_id:
        return await msg.reply("ℹ️ Сейчас за вами не закреплена активная сделка, где ожидается ссылка.")
    await msg.reply("🔗 Пришлите одну ссылку на гарант-чат — я отправлю её участникам сделки в ЛС.")


@r.message(F.chat.type == "private", F.func(lambda m: m.from_user.id in st.awaiting_appeal), F.text)
async def collect_appeal_text(msg: Message) -> None:
    st.awaiting_appeal.discard(msg.from_user.id)

    appeal_text = (msg.text or "").strip()[:APPEAL_MAX_LEN]
    if not appeal_text:
        return await msg.reply(appeal_prompt_text())
    async with st.pool.acquire() as c:
        appeal_id = await c.fetchval(
            "INSERT INTO appeals (user_id, username, text) VALUES ($1, $2, $3) RETURNING id",
            msg.from_user.id, msg.from_user.username or "", appeal_text,
        )
        last = await c.fetchrow(
            "SELECT action, chat_id, reason, ts FROM action_logs "
            "WHERE target_id=$1 AND action NOT ILIKE 'APPEAL_%' AND (action ILIKE '%MUTE%' OR action ILIKE '%BAN%' OR action IN ('MUTE','BAN')) "
            "ORDER BY ts DESC LIMIT 1",
            msg.from_user.id,
        )

    if last and "BAN" in (last["action"] or "").upper():
        kb = InlineKeyboardMarkup(inline_keyboard=[[ 
            InlineKeyboardButton(text="✅ Разбанить", callback_data=f"appeal_unban:{appeal_id}"),
            InlineKeyboardButton(text="🚫 Оставить в бане", callback_data=f"appeal_keep:{appeal_id}"),
        ]])
        punishment_line = "🚫 <b>Последнее наказание:</b> бан"
    else:
        kb = InlineKeyboardMarkup(inline_keyboard=[[ 
            InlineKeyboardButton(text="✅ Размьютить", callback_data=f"appeal_unmute:{appeal_id}"),
            InlineKeyboardButton(text="🔇 Оставить в мьюте", callback_data=f"appeal_keep:{appeal_id}"),
        ]])
        punishment_line = "🔇 <b>Последнее наказание:</b> мут" if last else "ℹ️ <b>Последнее наказание:</b> не найдено в логах"

    last_line = (
        f"\n💬 Chat ID: <code>{last['chat_id']}</code>"
        f"\n⚡ Action: <code>{esc(last['action'])}</code>"
        f"\n📝 Reason: <i>{esc(last['reason'] or '—')}</i>"
    ) if last else ""

    username = f"@{msg.from_user.username}" if msg.from_user.username else "—"
    notify_text = (
        f"🧾 <b>Новая апелляция #{appeal_id}</b>\n\n"
        f"👤 Пользователь: {mention(msg.from_user)}\n"
        f"🆔 ID: <code>{msg.from_user.id}</code>\n"
        f"🔤 Username: {username}\n\n"
        f"{punishment_line}{last_line}\n\n"
        f"<b>Текст апелляции:</b>\n<blockquote>{esc(appeal_text)}</blockquote>\n\n"
        f"Выберите решение кнопкой ниже — бот сам выполнит действие."
    )

    sent_count = 0
    for uid in set(SUPER_ADMINS) | set(st.mods):
        try:
            await bot.send_message(uid, notify_text, reply_markup=kb)
            sent_count += 1
        except Exception as e:
            log.warning("Апелляция #%s — не удалось уведомить %s: %s", appeal_id, uid, e)

    log.info("Апелляция #%s отправлена %d получателям", appeal_id, sent_count)
    await msg.reply(
        f"✅ Апелляция #{appeal_id} направлена на рассмотрение.\n"
        f"⏳ Ожидайте решения администрации."
    )


@r.callback_query(F.data.startswith("appeal_"))
async def cb_appeal(cq: CallbackQuery) -> None:
    if cq.from_user.id not in SUPER_ADMINS and cq.from_user.id not in st.mods:
        return await cq.answer("⛔ Только для супер-админов и модераторов.", show_alert=True)

    action, appeal_id_str = cq.data.split(":", 1)
    appeal_id = int(appeal_id_str)

    async with st.pool.acquire() as c:
        appeal = await c.fetchrow("SELECT user_id, username, status FROM appeals WHERE id=$1", appeal_id)
        if not appeal:
            return await cq.answer("Апелляция не найдена.", show_alert=True)
        if appeal["status"] != "open":
            return await cq.answer(f"Уже рассмотрено: {appeal['status']}", show_alert=True)
        last = await c.fetchrow(
            "SELECT action, chat_id FROM action_logs "
            "WHERE target_id=$1 AND action NOT ILIKE 'APPEAL_%' AND (action ILIKE '%MUTE%' OR action ILIKE '%BAN%' OR action IN ('MUTE','BAN')) "
            "ORDER BY ts DESC LIMIT 1",
            appeal["user_id"],
        )

    user_id = appeal["user_id"]
    if action == "appeal_unmute":
        if not last:
            return await cq.answer("Не найден чат последнего мута.", show_alert=True)
        await unmute_user(bot, last["chat_id"], user_id)
        await allow_twin_user(last["chat_id"], user_id, cq.from_user.id)
        await db_log("APPEAL_UNMUTE", cq.from_user.id, user_id, last["chat_id"], f"Апелляция #{appeal_id}")
        status = "accepted_unmute"
        result = "✅ Размьючен"
        user_msg = "✅ Апелляция принята. Мут снят."
    elif action == "appeal_unban":
        if not last:
            return await cq.answer("Не найден чат последнего бана.", show_alert=True)
        await bot.unban_chat_member(last["chat_id"], user_id)
        st.banned_users[last["chat_id"]].discard(user_id)
        await allow_twin_user(last["chat_id"], user_id, cq.from_user.id)
        await db_log("APPEAL_UNBAN", cq.from_user.id, user_id, last["chat_id"], f"Апелляция #{appeal_id}")
        status = "accepted_unban"
        result = "✅ Разбанен"
        user_msg = "✅ Апелляция принята. Бан снят."
    elif action == "appeal_keep":
        chat_id = last["chat_id"] if last else 0
        await db_log("APPEAL_KEEP", cq.from_user.id, user_id, chat_id, f"Апелляция #{appeal_id}")
        status = "rejected_keep"
        result = "🔒 Оставлено"
        user_msg = "❌ Апелляция отклонена. Наказание оставлено."
    else:
        return

    async with st.pool.acquire() as c:
        await c.execute(
            "UPDATE appeals SET status=$1, resolved_by=$2, resolved_at=NOW() WHERE id=$3",
            status, cq.from_user.id, appeal_id,
        )

    try:
        await bot.send_message(user_id, user_msg)
    except Exception:
        pass

    await cq.message.edit_text(
        cq.message.text + f"\n\n{result} — {mention(cq.from_user)}",
        reply_markup=None,
    )
    await cq.answer("Решение выполнено.")


@r.message(F.chat.type == "private")
async def garant_link_private(msg: Message) -> None:
    # Пропускаем команды — они обрабатываются своими хендлерами
    if (msg.text or "").strip().startswith("/"):
        return
    if msg.from_user.id not in st.garants and msg.from_user.id not in SUPER_ADMINS:
        return
    deal_id = st.garant_pending_deal.get(msg.from_user.id)
    if not deal_id:
        return
    text = (msg.text or msg.caption or "").strip()
    if not text:
        return
    m = re.search(r"https?://t\.me/[^\s]+", text, re.I)
    if not m:
        return await msg.reply("❌ Не вижу Telegram-ссылку. Пришлите ссылку вида <code>https://t.me/...</code> в одном сообщении.")
    deal_link = m.group(0)
    st.deal_links[deal_id] = deal_link

    body = st.deal_participants.get(deal_id, "")
    chat_id = int(deal_id.split("_", 1)[0])
    delivered, failed_users = await deliver_deal_link_private_only(deal_id, chat_id, deal_link, body)

    try:
        base_text = (
            f"✅ <b>Ссылка отправлена</b>\n\n"
            f"📨 Доставлено в ЛС: <b>{delivered}</b>"
        )
        if not failed_users:
            await bot.send_message(chat_id, base_text)
        elif len(failed_users) == 1:
            await bot.send_message(
                chat_id,
                base_text + "\n\n"
                + f"⚠️ {failed_users[0]}, запустите бота через <code>/start</code>, чтобы получить ссылку в ЛС от бота."
            )
        else:
            mentions = " и ".join(failed_users[:2]) if len(failed_users) == 2 else ", ".join(failed_users)
            await bot.send_message(
                chat_id,
                base_text + "\n\n"
                + f"⚠️ {mentions}, запустите бота через <code>/start</code>, чтобы получить ссылку в ЛС от бота."
            )
    except Exception:
        pass

    for admin_uid in set(SUPER_ADMINS) | set(st.mods):
        try:
            await bot.send_message(
                admin_uid,
                f"🤖 <b>Сделка: ссылка отправлена</b>\n\n"
                f"🆔 Сделка: <code>{deal_id}</code>\n"
                f"👤 Гарант: {mention(msg.from_user)}\n"
                f"📨 Получателей: <b>{delivered}</b>\n"
                f"🔗 Ссылка: <code>{esc(deal_link)}</code>"
            )
        except Exception:
            pass

    st.garant_pending_deal.pop(msg.from_user.id, None)
    st.deal_status[deal_id] = "link_sent"
    await msg.reply("✅ Ссылка сохранена. Бот отправил её участникам сделки в ЛС.")



@r.callback_query(F.data == "show_rules")
async def cb_rules(cq: CallbackQuery) -> None:
    await cq.message.answer(build_rules_text())
    await cq.answer()


@r.callback_query(F.data == "show_help")
async def cb_help(cq: CallbackQuery) -> None:
    await cq.message.answer(ADMIN_HELP_TEXT)
    await cq.answer()


@r.message(Command("rules"))
async def cmd_rules(msg: Message) -> None:
    await msg.reply(build_rules_text())


@r.message(Command("help"))
async def cmd_help(msg: Message) -> None:
    await msg.reply(ADMIN_HELP_TEXT)


@r.message(Command("ping"))
async def cmd_ping(msg: Message) -> None:
    t0   = time.monotonic()
    sent = await msg.reply("🏓 Pong!")
    ms   = int((time.monotonic() - t0) * 1000)
    try:
        await sent.edit_text(f"🏓 Pong! <b>{ms} мс</b>")
    except Exception:
        pass


@r.message(Command("id"))
async def cmd_id(msg: Message) -> None:
    if msg.reply_to_message and msg.reply_to_message.from_user:
        u = msg.reply_to_message.from_user
        await msg.reply(
            f"🆔 <b>ID пользователя</b>\n\n"
            f"👤 {mention(u)}\n"
            f"📌 ID: <code>{u.id}</code>\n"
            f"🔤 Username: {'@' + u.username if u.username else '—'}"
        )
    else:
        u = msg.from_user
        await msg.reply(
            f"🆔 <b>Ваш ID</b>\n\n"
            f"👤 {mention(u)}\n"
            f"📌 ID: <code>{u.id}</code>\n"
            f"🔤 Username: {'@' + u.username if u.username else '—'}\n\n"
            f"<i>Tip: reply на сообщение другого пользователя, чтобы узнать его ID.</i>"
        )


@r.message(Command("stats"))
async def cmd_stats(msg: Message) -> None:
    if msg.chat.type not in ("group", "supergroup"):
        return await msg.reply("❌ Только в группах.")
    chat_id = msg.chat.id
    async with st.pool.acquire() as c:
        total_warns   = await c.fetchval("SELECT COALESCE(SUM(warns),0) FROM warnings WHERE chat_id=$1", chat_id) or 0
        total_actions = await c.fetchval("SELECT COUNT(*) FROM action_logs WHERE chat_id=$1", chat_id) or 0
        mutes_count   = await c.fetchval("SELECT COUNT(*) FROM action_logs WHERE chat_id=$1 AND action LIKE '%MUTE%'", chat_id) or 0
        bans_count    = await c.fetchval("SELECT COUNT(*) FROM action_logs WHERE chat_id=$1 AND action LIKE '%BAN%'", chat_id) or 0
        warned_users  = await c.fetchval("SELECT COUNT(*) FROM warnings WHERE chat_id=$1 AND warns>0", chat_id) or 0
        twin_count    = await c.fetchval("SELECT COUNT(*) FROM twin_accounts WHERE chat_id=$1", chat_id) or 0
    try:
        members = await bot.get_chat_member_count(chat_id)
    except Exception:
        members = "?"
    await msg.reply(
        f"📊 <b>Статистика чата</b>\n\n"
        f"👥 Участников: <b>{members}</b>\n"
        f"⚠️ Всего варнов выдано: <b>{total_warns}</b>\n"
        f"👤 Пользователей с варнами: <b>{warned_users}</b>\n"
        f"🔇 Мутов: <b>{mutes_count}</b>\n"
        f"🚫 Банов: <b>{bans_count}</b>\n"
        f"👥 Твинков помечено: <b>{twin_count}</b>\n"
        f"📋 Всего действий мод.: <b>{total_actions}</b>\n\n"
        f"🛡 Гарантов: <b>{len(st.garants)}</b> | "
        f"Модов: <b>{len(st.mods)}</b> | "
        f"Адм.: <b>{len(st.admins)}</b>"
    )


@r.message(Command("whois"))
async def cmd_whois(msg: Message) -> None:
    if msg.chat.type not in ("group", "supergroup"):
        return
    uid = msg.from_user.id
    if not is_bot_admin(uid) and not await is_chat_admin(bot, msg.chat.id, uid):
        return await msg.reply("⛔ Только для модераторов.")
    target = None
    if msg.reply_to_message and msg.reply_to_message.from_user:
        target = msg.reply_to_message.from_user
    else:
        parts = (msg.text or "").split(None, 1)
        if len(parts) > 1:
            target = await resolve_user(bot, msg.chat.id, parts[1].strip())
    if not target:
        return await msg.reply("❌ Укажи пользователя: reply или <code>/whois @username</code>")
    chat_id = msg.chat.id
    warns   = await db_warns_get(chat_id, target.id)
    async with st.pool.acquire() as c:
        last_actions = await c.fetch(
            "SELECT action, reason, ts FROM action_logs "
            "WHERE target_id=$1 AND chat_id=$2 ORDER BY ts DESC LIMIT 3",
            target.id, chat_id,
        )
        twin_rows = await c.fetch(
            "SELECT twin_of FROM twin_accounts WHERE user_id=$1 AND chat_id=$2",
            target.id, chat_id,
        )
    roles = []
    if target.id in SUPER_ADMINS: roles.append("👑 Супер-Админ")
    if target.id in st.garants:   roles.append("🛡 Гарант")
    if target.id in st.mods:      roles.append("🔧 Модератор")
    if target.id in st.admins:    roles.append("👮 Администратор")

    role_str  = " | ".join(roles) if roles else "👤 Обычный участник"
    twin_str  = ""
    if twin_rows:
        twin_ids = [str(r["twin_of"]) for r in twin_rows]
        twin_str = f"\n👥 Твинк аккаунта: {', '.join(f'<code>{t}</code>' for t in twin_ids)}"
    hist_lines = []
    for row in last_actions:
        ts_str = row["ts"].strftime("%d.%m %H:%M") if row["ts"] else "?"
        hist_lines.append(f"  • <code>{row['action']}</code> [{ts_str}] — <i>{esc(row['reason'] or '—')}</i>")
    hist_str  = "\n".join(hist_lines) if hist_lines else "  Нет действий"
    uname_str = f"@{target.username}" if target.username else "—"
    await msg.reply(
        f"🔍 <b>Информация о пользователе</b>\n\n"
        f"👤 {mention(target)}\n"
        f"🆔 ID: <code>{target.id}</code>\n"
        f"🔤 Username: {uname_str}\n"
        f"🏷 Роль: {role_str}{twin_str}\n\n"
        f"⚠️ Варны: <b>{warns}/3</b>\n\n"
        f"📋 <b>Последние действия:</b>\n{hist_str}"
    )


@r.message(Command("history"))
async def cmd_history(msg: Message) -> None:
    if msg.chat.type not in ("group", "supergroup"):
        return
    uid = msg.from_user.id
    if not is_bot_admin(uid) and not await is_chat_admin(bot, msg.chat.id, uid):
        return await msg.reply("⛔ Только для модераторов.")
    target = None
    if msg.reply_to_message and msg.reply_to_message.from_user:
        target = msg.reply_to_message.from_user
    else:
        parts = (msg.text or "").split(None, 1)
        if len(parts) > 1:
            target = await resolve_user(bot, msg.chat.id, parts[1].strip())
    if not target:
        return await msg.reply("❌ Укажи пользователя: reply или <code>/history @username</code>")
    chat_id = msg.chat.id
    async with st.pool.acquire() as c:
        rows = await c.fetch(
            "SELECT action, reason, ts FROM action_logs "
            "WHERE target_id=$1 AND chat_id=$2 ORDER BY ts DESC LIMIT 15",
            target.id, chat_id,
        )
        warn_rows = await c.fetch(
            "SELECT warn_number, reason, ts FROM warn_history "
            "WHERE user_id=$1 AND chat_id=$2 ORDER BY ts DESC LIMIT 5",
            target.id, chat_id,
        )
    if not rows and not warn_rows:
        return await msg.reply(f"📋 У {mention(target)} нет истории нарушений в этом чате.")
    lines = [f"📋 <b>История нарушений</b> — {mention(target)}\n"]
    if warn_rows:
        lines.append("⚠️ <b>Варны:</b>")
        for w in warn_rows:
            ts_str = w["ts"].strftime("%d.%m.%Y %H:%M") if w["ts"] else "?"
            lines.append(f"  #{w['warn_number']} [{ts_str}] — <i>{esc(w['reason'] or '—')}</i>")
    if rows:
        lines.append("\n📋 <b>Действия модераторов:</b>")
        for row in rows:
            ts_str = row["ts"].strftime("%d.%m.%Y %H:%M") if row["ts"] else "?"
            lines.append(
                f"  • <code>{row['action']}</code> [{ts_str}]"
                + (f" — <i>{esc(row['reason'])}</i>" if row["reason"] else "")
            )
    await msg.reply("\n".join(lines))


@r.message(Command("топ"))
async def cmd_top(msg: Message) -> None:
    if msg.chat.type not in ("group", "supergroup"):
        return
    uid = msg.from_user.id
    if not is_bot_admin(uid) and not await is_chat_admin(bot, msg.chat.id, uid):
        return await msg.reply("⛔ Только для модераторов.")
    chat_id = msg.chat.id
    async with st.pool.acquire() as c:
        rows = await c.fetch(
            "SELECT user_id, warns FROM warnings "
            "WHERE chat_id=$1 AND warns>0 ORDER BY warns DESC LIMIT 10",
            chat_id,
        )
    if not rows:
        return await msg.reply("✅ Нарушителей нет! Чат чистый 🎉")
    lines  = ["🏆 <b>Топ нарушителей чата</b>\n"]
    medals = ["🥇", "🥈", "🥉"]
    for i, row in enumerate(rows):
        medal = medals[i] if i < 3 else f"{i+1}."
        uid_r = row["user_id"]
        warns = row["warns"]
        lines.append(
            f"{medal} <a href='tg://user?id={uid_r}'>{uid_r}</a> — "
            f"<b>{warns}</b> {'варн' if warns==1 else 'варна' if 2<=warns<=4 else 'варнов'}"
        )
    await msg.reply("\n".join(lines))


@r.message(F.text.regexp(r"(?i)^твинк(?:\s|$)"))
@r.message(Command("твинк"))
async def cmd_mark_twin(msg: Message) -> None:
    if msg.chat.type not in ("group", "supergroup"):
        return
    uid = msg.from_user.id
    if not is_bot_admin(uid) and not await is_chat_admin(bot, msg.chat.id, uid):
        return await msg.reply("⛔ Только для модераторов.")
    if not msg.reply_to_message or not msg.reply_to_message.from_user:
        return await msg.reply(
            "❌ Reply на сообщение твинка + <code>твинк</code>"
        )
    twin_user = msg.reply_to_message.from_user
    parts = (msg.text or "").split(None, 1)
    chat_id   = msg.chat.id

    # Новый короткий режим: reply + "твинк" без указания оригинала
    if len(parts) < 2:
        if twin_user.is_bot:
            return await msg.reply("❌ Нельзя мутить бота.")
        if await is_chat_admin(bot, chat_id, twin_user.id):
            return await msg.reply("🛡 Нельзя мутить админа.")
        deleted_preview = make_deleted_message_preview(msg.reply_to_message)
        try:
            await mute_user(bot, chat_id, twin_user.id, None)
            await safe_delete(msg.reply_to_message)
        except Exception:
            pass
        await db_log("TWIN_MUTE_MANUAL", uid, twin_user.id, chat_id, "Твинк без указания оригинала")
        await msg.reply(
            f"⚠️ Обнаружен твинк.\n"
            f"🔇 {mention(twin_user)} — мут <b>до снятия администрацией</b>.\n"
            f"📌 Причина: твинк\n"
            f"<code>uid:{twin_user.id}</code>" + APPEAL_HINT
        )
        await notify_auto_action(
            bot=bot,
            chat_id=chat_id,
            chat_title=msg.chat.title or "Группа",
            target_id=twin_user.id,
            target_name=twin_user.first_name or str(twin_user.id),
            action="🔇 Мут навсегда, до решения администрации (твинк)",
            reason="Твинк, ручная пометка без оригинала",
            duration="до снятия администрацией",
            deleted_preview=deleted_preview,
        )
        return

    orig_raw  = parts[1].strip()
    orig_user = await resolve_user(bot, chat_id, orig_raw)
    if not orig_user:
        clean = orig_raw.lstrip("@")
        if clean.lstrip("-").isdigit():
            orig_id = int(clean)
        else:
            return await msg.reply(f"❌ Не найден: <code>{esc(orig_raw)}</code>")
    else:
        orig_id = orig_user.id
    if twin_user.id == orig_id:
        return await msg.reply("❌ Нельзя пометить пользователя твинком самого себя.")
    async with st.pool.acquire() as c:
        await c.execute(
            "INSERT INTO twin_accounts (user_id, twin_of, chat_id, added_by) "
            "VALUES ($1,$2,$3,$4) ON CONFLICT (user_id, twin_of, chat_id) DO NOTHING",
            twin_user.id, orig_id, chat_id, uid,
        )
    # Направленная связь: twin_user является твинком orig_id (не наоборот)
    st.twins[orig_id].add(twin_user.id)
    st.twin_of[twin_user.id].add(orig_id)
    orig_str = mention(orig_user) if orig_user else f"<code>{orig_id}</code>"
    await msg.reply(
        f"👥 <b>Твинк помечен!</b>\n\n"
        f"🔗 {mention(twin_user)} → твинк {orig_str}\n\n"
        f"⚠️ Если оригинал в муте/бане — твинк будет автоматически наказан."
    )
    await db_log("MARK_TWIN", uid, twin_user.id, chat_id, f"Твинк пользователя {orig_id}")


# ─────────────────────────────────────────────────────────
# ROLE COMMANDS
# ─────────────────────────────────────────────────────────

def _sa_only(func):
    async def wrapper(msg: Message) -> None:
        if msg.from_user.id not in SUPER_ADMINS:
            return
        await func(msg)
    return wrapper


async def _cmd_add_role(msg: Message, role_key: str) -> None:
    table, mem = _ROLE_MAP[role_key]
    if not msg.reply_to_message or not msg.reply_to_message.from_user:
        return await msg.reply(f"❌ Сделай <b>reply</b> на сообщение пользователя.")
    user = msg.reply_to_message.from_user
    if user.is_bot:
        return await msg.reply("❌ Нельзя назначить бота.")
    await role_add(table, mem, user.id, user.username or "", msg.from_user.id)
    uname_str = f"@{user.username}" if user.username else mention(user)
    await msg.reply(f"✅ {uname_str} добавлен как {role_key}!\n🆔 ID: <code>{user.id}</code>")
    if role_key == "гаранта":
        try:
            await bot.send_message(
                user.id,
                "🛡 <b>Вы назначены гарантом!</b>\n\n"
                "Теперь при вызове через <code>/адм</code> вы будете получать "
                "уведомления о запросах на сделки прямо в личные сообщения.\n\n"
                "✅ Чтобы принять сделку — нажмите кнопку <b>«Принять сделку»</b>."
            )
        except TelegramForbiddenError:
            await msg.reply(f"⚠️ Не удалось уведомить {uname_str} в ЛС. Попросите написать /start")
        except Exception as e:
            log.warning("Не удалось уведомить гаранта %s: %s", user.id, e)


async def _cmd_remove_role(msg: Message, role_key: str) -> None:
    table, mem = _ROLE_MAP[role_key]
    parts = (msg.text or "").split(None, 1)
    if len(parts) < 2:
        return await msg.reply(f"❌ Формат: <code>/удалить_{role_key} @username</code>")
    raw = parts[1].lstrip("@").strip()
    async with st.pool.acquire() as c:
        row = await c.fetchrow(
            f"SELECT user_id, username FROM {table} WHERE "
            f"{'user_id=$1' if raw.lstrip('-').isdigit() else 'LOWER(username)=LOWER($1)'}",
            int(raw) if raw.lstrip("-").isdigit() else raw,
        )
    if not row:
        return await msg.reply(f"❌ Не найден: <code>{raw}</code>")
    await role_remove(table, mem, row["user_id"])
    await msg.reply(f"✅ <b>@{row['username'] or raw}</b> удалён из {role_key}.")


@r.message(Command("добавить_гаранта"))
@_sa_only
async def cmd_add_garant(msg: Message): await _cmd_add_role(msg, "гаранта")

@r.message(Command("удалить_гаранта"))
@_sa_only
async def cmd_rem_garant(msg: Message): await _cmd_remove_role(msg, "гаранта")

@r.message(Command("добавить_модератора"))
@_sa_only
async def cmd_add_mod(msg: Message): await _cmd_add_role(msg, "модератора")

@r.message(Command("удалить_модератора"))
@_sa_only
async def cmd_rem_mod(msg: Message): await _cmd_remove_role(msg, "модератора")

@r.message(Command("добавить_администратора"))
@_sa_only
async def cmd_add_admin(msg: Message): await _cmd_add_role(msg, "администратора")

@r.message(Command("удалить_администратора"))
@_sa_only
async def cmd_rem_admin(msg: Message): await _cmd_remove_role(msg, "администратора")





@r.message(Command("админы"))
async def cmd_list_admins(msg: Message) -> None:
    async with st.pool.acquire() as c:
        gar  = await c.fetch("SELECT username FROM garant_admins ORDER BY added_at")
        mods = await c.fetch("SELECT username FROM moderators ORDER BY added_at")
        adms = await c.fetch("SELECT username FROM administrators ORDER BY added_at")
    def fmt(rows) -> str:
        items = [f"@{r['username']}" for r in rows if r["username"]]
        return " ".join(items) if items else "—"
    await msg.reply(
        f"💬 <b>Модераторы:</b> {fmt(mods)}\n"
        f"🤝 <b>Гаранты:</b> {fmt(gar)}\n"
        f"👮 <b>Администраторы:</b> {fmt(adms)}\n"
        f"👑 <b>Владельцы:</b> @mrtley @Timmy_Falcon"
    )


@r.message(Command("set_welcome"))
async def cmd_set_welcome(msg: Message) -> None:
    if msg.from_user.id not in SUPER_ADMINS:
        return
    parts = (msg.text or "").split(None, 1)
    if len(parts) < 2:
        return await msg.reply("❌ Пример: <code>/set_welcome Привет, {name}!</code>")
    await db_set_welcome(msg.chat.id, parts[1].strip())
    await msg.reply(f"✅ Приветствие обновлено:\n\n{parts[1].strip()}")


@r.message(Command("reset_welcome"))
async def cmd_reset_welcome(msg: Message) -> None:
    if msg.from_user.id not in SUPER_ADMINS:
        return
    await db_set_welcome(msg.chat.id, None)
    await msg.reply("✅ Приветствие сброшено на стандартное.")


@r.message(F.new_chat_members)
async def on_new_member(msg: Message) -> None:
    for user in msg.new_chat_members:
        if user.is_bot:
            continue
        chat_id = msg.chat.id
        tmpl = await db_get_welcome(chat_id)
        if not tmpl:
            tmpl = "👋 Добро пожаловать, {name}!"
        name = esc(user.first_name or "Гость")
        welcome_text = tmpl.format(name=name, id=user.id)

        # Кнопка «📜 Правила» — показывает правила чата по нажатию
        kb = InlineKeyboardMarkup(inline_keyboard=[[
            InlineKeyboardButton(
                text="📜 Правила",
                callback_data=f"show_rules:{chat_id}",
            ),
        ]])
        try:
            await msg.answer(welcome_text, reply_markup=kb)
        except Exception as _e:
            log.warning("welcome: не смог отправить: %s", _e)


# ─────────────────────────────────────────────────────────
# /адм — вызов гаранта
# ─────────────────────────────────────────────────────────

@r.callback_query(F.data.startswith("show_rules:"))
async def cb_show_rules(cq: CallbackQuery) -> None:
    """Кнопка «📜 Правила» в приветствии — показывает правила чата."""
    chat_id = int(cq.data.split(":")[1])
    rules_text = build_rules_text()
    if not rules_text or rules_text.strip() == "":
        return await cq.answer("Правила ещё не заданы.", show_alert=True)
    try:
        # Отвечаем в личку нажавшему — не засоряем чат
        await cq.answer()
        await cq.message.reply(rules_text)
    except Exception as _e:
        log.warning("cb_show_rules: %s", _e)
        await cq.answer("Не удалось показать правила.", show_alert=True)


@r.message(Command("адм"))
async def cmd_adm(msg: Message) -> None:
    if msg.chat.type not in ("group", "supergroup"):
        return

    caller = msg.from_user

    # Только reply-режим
    if not msg.reply_to_message or not msg.reply_to_message.from_user:
        return await msg.reply(
            "❌ Команду нужно использовать reply на сообщение второго участника сделки.\n\n"
            "Пример: ответьте на сообщение партнёра и напишите:\n"
            "<code>/адм хочу купить аккаунт за 3000₽</code>"
        )

    partner = msg.reply_to_message.from_user

    if partner.is_bot:
        return await msg.reply("❌ Нельзя вызвать гаранта reply на бота.")

    if partner.id == caller.id:
        return await msg.reply("❌ Нельзя вызвать гаранта reply на самого себя.")

    # Текст сделки — всё после команды
    body_parts = (msg.text or "").split(None, 1)
    details = body_parts[1].strip() if len(body_parts) > 1 else ""
    if not details:
        return await msg.reply(
            "❌ Укажите суть сделки после команды.\n\n"
            "Пример: <code>/адм хочу купить аккаунт за 3000₽</code>"
        )

    garant_ids, _ = await get_cached_garant_data()
    if not garant_ids:
        return await msg.reply("⚠️ Сейчас нет активных гарантов в базе. Сообщите владельцу/админу.")

    # Формируем имена для карточки
    caller_name  = esc(caller.first_name or str(caller.id))
    partner_name = esc(partner.first_name or str(partner.id))
    caller_ref   = f"@{caller.username}" if caller.username else f"id{caller.id}"
    partner_ref  = f"@{partner.username}" if partner.username else f"id{partner.id}"

    deal_role_key, deal_role_label = detect_deal_role(details)
    deal_amount = extract_deal_amount(details)

    chat_link = f"https://t.me/c/{str(msg.chat.id).replace('-100','')}/{msg.message_id}"
    deal_id   = f"{msg.chat.id}_{msg.message_id}"

    # Сохраняем uid обоих участников — доставка без resolve_user
    st.deal_uids[deal_id]         = [caller.id, partner.id]
    st.deal_participants[deal_id] = f"{caller_ref} сделка с {partner_ref}: {details}"
    st.deal_status[deal_id]       = "created"
    st.deal_origin_message[deal_id] = msg.message_id

    kb_garant = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ Принять сделку", callback_data=f"deal_accept:{deal_id}:{msg.chat.id}")],
        [
            InlineKeyboardButton(text="📝 Запросить уточнение", callback_data=f"deal_clarify:{deal_id}:{msg.chat.id}"),
            InlineKeyboardButton(text="❌ Отклонить", callback_data=f"deal_decline:{deal_id}:{msg.chat.id}"),
        ],
    ])

    request_card = (
        f"🆕 <b>Новый запрос гаранту</b>\n\n"
        f"👤 Инициатор: <a href='tg://user?id={caller.id}'>{caller_name}</a> ({caller_ref})\n"
        f"🤝 Контрагент: <a href='tg://user?id={partner.id}'>{partner_name}</a> ({partner_ref})\n"
        f"🏷 Тип сделки: <b>{deal_role_label}</b>\n"
        f"💰 Сумма: <b>{esc(deal_amount)}</b>\n"
        f"🧾 Детали: <blockquote>{esc(details)}</blockquote>\n"
        f"💬 Чат: <b>{esc(msg.chat.title or 'Группа')}</b>\n\n"
        f"👉 <a href='{chat_link}'>Перейти к сообщению</a>"
    )

    notified_count = 0
    for g_uid in garant_ids:
        try:
            await bot.send_message(g_uid, request_card, reply_markup=kb_garant)
            notified_count += 1
        except TelegramForbiddenError:
            log.warning("Гарант %s заблокировал бота", g_uid)
        except Exception as e:
            log.warning("ЛС гаранту %s не доставлено: %s", g_uid, e)

    if notified_count == 0:
        return await msg.reply(
            "⚠️ Не удалось доставить запрос ни одному гаранту.\n"
            "Попросите гаранта написать боту <code>/start</code> в ЛС."
        )

    await msg.reply(
        f"✅ <b>Запрос гаранту отправлен</b>\n\n"
        f"👤 Инициатор: {caller_name} ({caller_ref})\n"
        f"🤝 Контрагент: {partner_name} ({partner_ref})\n"
        f"🏷 Тип сделки: <b>{deal_role_label}</b>\n"
        f"💰 Сумма: <b>{esc(deal_amount)}</b>\n"
        f"🧾 Детали: <blockquote>{esc(details)}</blockquote>\n\n"
        f"📨 Уведомлено гарантов: <b>{notified_count}</b>\n"
        f"⏳ Ожидайте, пока один из гарантов примет сделку."
    )


def _is_not_mod_command(msg: Message) -> bool:
    """Фильтр: True если сообщение НЕ является мод-командой."""
    raw = (msg.text or "").strip()
    if not raw:
        return True
    first_word = raw.lstrip("/").split(None, 1)[0].lower()
    return first_word not in _MOD_COMMANDS and first_word not in {"твинк", "id", "ping"}


@r.message(F.chat.type.in_({"group", "supergroup"}), F.reply_to_message, _is_not_mod_command)
async def deal_clarification_reply(msg: Message) -> None:
    if not msg.from_user or not msg.text:
        return

    raw_text = (msg.text or "").strip()

    reply_msg = msg.reply_to_message
    if not reply_msg or reply_msg.message_id is None:
        return

    deal_id = None
    for did, mid in st.deal_origin_message.items():
        if mid == reply_msg.message_id and msg.chat.id == int(did.split("_", 1)[0]):
            deal_id = did
            break
    if not deal_id:
        return
    if st.deal_status.get(deal_id) != "clarification_requested":
        return

    body = raw_text
    if len(body) < 5:
        return

    current = st.deal_participants.get(deal_id, "")
    updated = current + " | Уточнение: " + body
    st.deal_participants[deal_id] = updated
    st.deal_status[deal_id] = "clarified"
    garant_uid = st.deal_clarification_target.get(deal_id)

    pretty = (
        f"✅ <b>Уточнение получено</b>\n\n"
        f"👤 От: {mention(msg.from_user)}\n"
        f"🧾 Уточнение:\n<blockquote>{esc(body)}</blockquote>\n\n"
        f"⏳ Гарант может повторно принять сделку."
    )
    try:
        await bot.send_message(msg.chat.id, pretty)
    except Exception:
        pass

    if garant_uid:
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="✅ Принять уточнённую сделку", callback_data=f"deal_accept:{deal_id}:{msg.chat.id}")],
            [InlineKeyboardButton(text="❌ Отклонить", callback_data=f"deal_decline:{deal_id}:{msg.chat.id}")],
        ])
        try:
            await bot.send_message(
                garant_uid,
                f"📝 <b>Поступило уточнение по сделке</b>\n\n"
                f"🆔 Сделка: <code>{deal_id}</code>\n"
                f"👤 Отправил: {mention(msg.from_user)}\n"
                f"🧾 Текст:\n<blockquote>{esc(body)}</blockquote>\n\n"
                f"Нажмите кнопку ниже, чтобы снова принять сделку.",
                reply_markup=kb,
            )
        except Exception:
            pass


# ─────────────────────────────────────────────────────────
# MAIN GROUP MESSAGE HANDLER
# ─────────────────────────────────────────────────────────

_MOD_COMMANDS = frozenset([
    "варн", "сброс", "варны", "мут", "размут", "бан", "разбан",
    "правила", "помощь", "команды", "лимит", "снять", "объяв", "purge",
    "автодействия",
])
# Двухсловные команды — проверяются отдельно после обычного парсинга
_MOD_COMMANDS_2W = frozenset([
    "разбан здесь", "размут здесь", "снять мат",
])


@r.message(F.chat.type.in_({"group", "supergroup"}))
async def group_handler(msg: Message) -> None:
    if not msg.from_user:
        return
    try:
        await _handle_group(msg)
    except TelegramBadRequest as e:
        log.warning("TG error: %s", e)
    except Exception as e:
        log.exception("Unhandled: %s", e)


async def _handle_group(msg: Message) -> None:
    uid     = msg.from_user.id
    chat_id = msg.chat.id
    text    = msg.text or msg.caption or ""

    caller_is_admin = await is_chat_admin(bot, chat_id, uid)
    caller_is_mod   = is_bot_admin(uid) or caller_is_admin

    # ── Загружаем настройки чата (кэш в памяти) ──────────
    cfg = await db_get_settings(chat_id)

    # ── Арабский/персидский текст → тихий бан ────────────
    if cfg.get("antiarabic", True) and not caller_is_mod and text:
        arabic_chars = _RE_ARABIC.findall(text)
        if len(arabic_chars) >= ARABIC_MIN_CHARS:
            deleted_preview = make_deleted_message_preview(msg)
            await safe_delete(msg)
            try:
                await bot.ban_chat_member(chat_id, uid)
                st.banned_users[chat_id].add(uid)
                remember_recent_punishment(chat_id, uid, "ban")
                _log_auto_ban(chat_id, msg.chat.title or "Группа", uid, msg.from_user.first_name or str(uid), "Арабский текст")
            except Exception:
                pass
            await db_log("AUTO_BAN_ARABIC", 0, uid, chat_id, "Арабский текст")
            for sa_id in SUPER_ADMINS:
                try:
                    await bot.send_message(
                        sa_id,
                        f"🚫 <b>Авто-бан (арабские символы)</b>\n\n"
                        f"💬 Чат: <b>{esc(msg.chat.title or 'Группа')}</b>\n"
                        f"👤 Пользователь: {mention(msg.from_user)} "
                        f"(<code>{uid}</code>)\n\n"
                        f"{deleted_preview}"
                    )
                except Exception:
                    pass
            return

    # ── Rate limit ────────────────────────────────────────
    if uid in st.rate_intervals and not caller_is_mod:
        interval = st.rate_intervals[uid]
        now_ts   = time.monotonic()
        last     = st.rate_last.get(uid, 0.0)
        if now_ts - last < interval:
            await safe_delete(msg)
            return
        st.rate_last[uid] = now_ts

    if not caller_is_mod:
        # Вычисляем хэш один раз для всех проверок
        msg_hash = _text_hash(text) if text else ""

        # Запоминаем message_id в историю последних сообщений юзера (до 5) —
        # используется для контекста модераторам при докс-угрозах и т.п.
        st.recent_msgs[chat_id][uid].append(msg.message_id)

        # ── Проверка вручную помеченных твинков ───────────
        if cfg.get("antitwin", True) and await check_manual_twins(bot, msg, uid, chat_id):
            return

        # ── Мат / оскорбления — ДО детектора твинков по тексту ──
        # Иначе, если кто-то уже писал точно такое же оскорбление раньше,
        # бот ошибочно ловил бы это как "твинк" (совпадение текста)
        # вместо простого удаления как оскорбления.
        if text and cfg.get("antimat", True):
            _mat_match = (
                _RE_FAMILY_INSULT.search(text) or
                _RE_DIRECT_INSULT.search(text) or
                _RE_MAT.search(text)
            )
            if _mat_match:
                if (chat_id, uid) in st.mat_silent_users:
                    # Юзер уже помечен — тихо удаляем, без сообщения и форварда
                    await safe_delete(msg)
                    await db_log("MAT_DELETE_SILENT", 0, uid, chat_id, "Авто-удаление (тихий режим)")
                elif msg_hash and (chat_id, uid, msg_hash) in st.hash_pardons:
                    pass  # конкретное сообщение прощено — пропускаем
                else:
                    # Первый раз — форвард модераторам + удаление
                    await _notify_mat(bot, msg, chat_id, uid, msg_hash or "")
                return

        # ── Проверка твинков по тексту ────────────────────
        if cfg.get("antitwin", True) and text and len(text) >= TWIN_MIN_LEN:
            if await check_twin_by_text(bot, msg, uid, chat_id, text):
                return

        # ── Файлы (документы) — удаляем в целях безопасности ──
        if cfg.get("antifiles", True) and msg.document:
            await safe_delete(msg)
            try:
                await msg.answer(
                    "🛡 <b>Файл удалён</b>\n\n"
                    f"👤 {mention(msg.from_user)}, ваш файл удалён "
                    "для безопасности других участников.\n"
                )
            except Exception:
                pass
            await db_log("AUTO_DELETE_FILE", 0, uid, chat_id, "Отправка файла (документа)")
            return

        # ── Спам «чат/ссылка в профиле» → мут 1 день ─────
        if cfg.get("antiprofilespam", True) and _RE_PROFILE_SPAM.search(text):
            if msg_hash and (chat_id, uid, msg_hash) in st.hash_pardons:
                pass  # прощено — пропускаем
            else:
                deleted_preview = make_deleted_message_preview(msg)
                hits = await db_ad_hit(chat_id, uid)
                mute_secs, mute_label = ad_mute_duration_by_hits(hits)
                await safe_delete(msg)
                try:
                    await mute_user(bot, chat_id, uid, mute_secs)
                except Exception:
                    pass
                reason = f"Реклама / чат в профиле (Правило 8), нарушение #{hits}"
                await db_log("AUTO_MUTE", 0, uid, chat_id, reason)
                asyncio.create_task(send_auto_notif(
                    chat_id,
                    f"🔇 {mention(msg.from_user)} — мут <b>{mute_label}</b>.\n"
                    f"📌 Правило 8: Реклама \n"
                    f"⚠️ Нарушений правила: <b>{hits}</b>\n"
                    f"<code>uid:{uid}</code>" + APPEAL_HINT,
                ))
                await notify_auto_action(
                    bot=bot,
                    chat_id=chat_id,
                    chat_title=msg.chat.title or "Группа",
                    target_id=uid,
                    target_name=msg.from_user.first_name or str(uid),
                    action="🔇 Мут",
                    reason=reason,
                    duration=mute_label,
                    deleted_preview=deleted_preview,
                    msg_hash=msg_hash,
                )
                if msg_hash:
                    _remember_text_hash(chat_id, msg_hash, uid, False)
                return

        # ── Эскорт / 18+ контент (Правило 4) ─────────────
        found_escort, escort_reason = has_escort_content(text)
        if found_escort and cfg.get("antiescort", True):
            if msg_hash and (chat_id, uid, msg_hash) in st.hash_pardons:
                pass
            else:
                deleted_preview = make_deleted_message_preview(msg)
                await safe_delete(msg)
                mute_secs = 86400
                mute_label = "1 день"
                try:
                    await mute_user(bot, chat_id, uid, mute_secs)
                except Exception:
                    pass
                reason = f"{escort_reason} (Правило 4)"
                await db_log("AUTO_MUTE", 0, uid, chat_id, reason)
                asyncio.create_task(send_auto_notif(
                    chat_id,
                    f"🔇 {mention(msg.from_user)} — мут <b>{mute_label}</b>.\n"
                    f"📌 Правило 4: 18+, эскорт и т.п.\n"
                    f"<code>uid:{uid}</code>" + APPEAL_HINT,
                ))
                await notify_auto_action(
                    bot=bot,
                    chat_id=chat_id,
                    chat_title=msg.chat.title or "Группа",
                    target_id=uid,
                    target_name=msg.from_user.first_name or str(uid),
                    action="🔇 Мут (эскорт/18+)",
                    reason=reason,
                    duration=mute_label,
                    deleted_preview=deleted_preview,
                    msg_hash=msg_hash,
                )
                if msg_hash:
                    _remember_text_hash(chat_id, msg_hash, uid, False)
                return

        # ── Азартные игры (Правило 1.2 со страницы правил) ──
        if cfg.get("antigambling", True) and has_gambling_content(text):
            if msg_hash and (chat_id, uid, msg_hash) in st.hash_pardons:
                pass
            else:
                deleted_preview = make_deleted_message_preview(msg)
                await safe_delete(msg)
                mute_secs, mute_label = 86400, "1 день"
                try:
                    await mute_user(bot, chat_id, uid, mute_secs)
                except Exception:
                    pass
                reason = "Зазывание в азартные игры"
                await db_log("AUTO_MUTE", 0, uid, chat_id, reason)
                asyncio.create_task(send_auto_notif(
                    chat_id,
                    f"🔇 {mention(msg.from_user)} — мут <b>{mute_label}</b>.\n"
                    f"📌 {reason}\n"
                    f"<code>uid:{uid}</code>" + APPEAL_HINT,
                ))
                await notify_auto_action(
                    bot=bot,
                    chat_id=chat_id,
                    chat_title=msg.chat.title or "Группа",
                    target_id=uid,
                    target_name=msg.from_user.first_name or str(uid),
                    action="🔇 Мут (азартные игры)",
                    reason=reason,
                    duration=mute_label,
                    deleted_preview=deleted_preview,
                    msg_hash=msg_hash,
                )
                if msg_hash:
                    _remember_text_hash(chat_id, msg_hash, uid, False)
                return

        # ── Попрошайничество (Правило 1.7 со страницы правил) ──
        if cfg.get("antibegging", True) and has_begging_content(text):
            if msg_hash and (chat_id, uid, msg_hash) in st.hash_pardons:
                pass
            else:
                deleted_preview = make_deleted_message_preview(msg)
                await safe_delete(msg)
                mute_secs, mute_label = 86400, "1 день"
                try:
                    await mute_user(bot, chat_id, uid, mute_secs)
                except Exception:
                    pass
                reason = "Попрошайничество"
                await db_log("AUTO_MUTE", 0, uid, chat_id, reason)
                asyncio.create_task(send_auto_notif(
                    chat_id,
                    f"🔇 {mention(msg.from_user)} — мут <b>{mute_label}</b>.\n"
                    f"📌 {reason}\n"
                    f"<code>uid:{uid}</code>" + APPEAL_HINT,
                ))
                await notify_auto_action(
                    bot=bot,
                    chat_id=chat_id,
                    chat_title=msg.chat.title or "Группа",
                    target_id=uid,
                    target_name=msg.from_user.first_name or str(uid),
                    action="🔇 Мут (попрошайничество)",
                    reason=reason,
                    duration=mute_label,
                    deleted_preview=deleted_preview,
                    msg_hash=msg_hash,
                )
                if msg_hash:
                    _remember_text_hash(chat_id, msg_hash, uid, False)
                return

        # ── Угроза докса/слива данных (без апелляции на странице) ──
        # Авто-мут НАВСЕГДА + пересылка супер-админам/модераторам на решение
        # (бан или снять как ложное срабатывание) — см. _notify_doxx_threat.
        if cfg.get("antidoxx", True) and has_doxx_threat(text):
            if msg_hash and (chat_id, uid, msg_hash) in st.hash_pardons:
                pass
            else:
                await _notify_doxx_threat(
                    bot, msg, chat_id, uid, msg_hash,
                    reason="Угроза доксом/сливом личных данных",
                )
                if msg_hash:
                    _remember_text_hash(chat_id, msg_hash, uid, False)
                return

        # ── Сомнительные услуги (2.3 со страницы правил) ────
        if cfg.get("antisuspicious", True) and has_suspicious_service(text):
            if msg_hash and (chat_id, uid, msg_hash) in st.hash_pardons:
                pass
            else:
                deleted_preview = make_deleted_message_preview(msg)
                hits = await db_ad_hit(chat_id, uid)
                mute_secs, mute_label = ad_mute_duration_by_hits(hits)
                await safe_delete(msg)
                try:
                    await mute_user(bot, chat_id, uid, mute_secs)
                except Exception:
                    pass
                reason = f"Сомнительные услуги, нарушение #{hits}"
                await db_log("AUTO_MUTE", 0, uid, chat_id, reason)
                asyncio.create_task(send_auto_notif(
                    chat_id,
                    f"🔇 {mention(msg.from_user)} — мут <b>{mute_label}</b>.\n"
                    f"📌 Сомнительные услуги\n"
                    f"⚠️ Нарушений: <b>{hits}</b>\n"
                    f"<code>uid:{uid}</code>" + APPEAL_HINT,
                ))
                await notify_auto_action(
                    bot=bot,
                    chat_id=chat_id,
                    chat_title=msg.chat.title or "Группа",
                    target_id=uid,
                    target_name=msg.from_user.first_name or str(uid),
                    action="🔇 Мут (сомнительные услуги)",
                    reason=reason,
                    duration=mute_label,
                    deleted_preview=deleted_preview,
                    msg_hash=msg_hash,
                )
                if msg_hash:
                    _remember_text_hash(chat_id, msg_hash, uid, False)
                return

        # ── Проверка рекламных ссылок ──────────────────────
        if await db_antilink_on(chat_id):
            all_entities = list(msg.entities or []) + list(msg.caption_entities or [])
            found_link, link_reason = has_ad_link(text, all_entities)

            if found_link:
                if msg_hash and (chat_id, uid, msg_hash) in st.hash_pardons:
                    pass
                else:
                    deleted_preview = make_deleted_message_preview(msg)
                    hits = await db_ad_hit(chat_id, uid)
                    mute_secs, mute_label = ad_mute_duration_by_hits(hits)
                    await safe_delete(msg)
                    try:
                        await mute_user(bot, chat_id, uid, mute_secs)
                    except Exception:
                        pass
                    reason = f"Реклама: {link_reason} (Правило 8), нарушение #{hits}"
                    await db_log("AUTO_MUTE", 0, uid, chat_id, reason)
                    asyncio.create_task(send_auto_notif(
                        chat_id,
                        f"🔇 {mention(msg.from_user)} — мут <b>{mute_label}</b>.\n"
                        f"📌 Правило 8: Реклама ({esc(link_reason)})\n"
                        f"⚠️ Нарушений правила: <b>{hits}</b>\n"
                        f"<code>uid:{uid}</code>" + APPEAL_HINT,
                    ))
                    await notify_auto_action(
                        bot=bot,
                        chat_id=chat_id,
                        chat_title=msg.chat.title or "Группа",
                        target_id=uid,
                        target_name=msg.from_user.first_name or str(uid),
                        action="🔇 Мут",
                        reason=reason,
                        duration=mute_label,
                        deleted_preview=deleted_preview,
                        msg_hash=msg_hash,
                    )
                    if msg_hash:
                        _remember_text_hash(chat_id, msg_hash, uid, False)
                    return

        return

    # ── Команды модераторов ───────────────────────────────
    clean = text.strip().lstrip("/")
    parts = clean.split(None, 2)   # до 3 частей: слово1 слово2 остаток
    if not parts:
        return

    # Проверяем двухсловные команды («разбан здесь», «размут здесь»...)
    _cmd2 = (parts[0] + " " + parts[1]).lower() if len(parts) >= 2 else ""
    if _cmd2 in _MOD_COMMANDS_2W:
        cmd      = _cmd2
        arg_tail = parts[2].strip() if len(parts) > 2 else ""
    else:
        cmd      = parts[0].lower()
        arg_tail = (parts[1] + (" " + parts[2] if len(parts) > 2 else "")).strip() if len(parts) > 1 else ""

    if cmd not in _MOD_COMMANDS and cmd not in _MOD_COMMANDS_2W:
        return

    if cmd == "правила":
        return await msg.reply(build_rules_text())
    if cmd in ("помощь", "команды"):
        return await msg.reply(ADMIN_HELP_TEXT)

    if cmd == "автодействия":
        return await msg.reply(
            _render_autopanel_section(chat_id, "mute"),
            reply_markup=_autopanel_keyboard(chat_id, "mute"),
        )

    if cmd == "объяв":
        if not arg_tail:
            return await msg.reply("❌ Укажи текст объявления.")
        sent = await msg.answer(f"📢 <b>Объявление</b>\n\n{arg_tail}")
        try:
            await bot.pin_chat_message(chat_id, sent.message_id)
        except Exception:
            pass
        await safe_delete(msg)
        return

    if cmd == "purge":
        if not msg.reply_to_message:
            return await msg.reply("❌ Reply на сообщение, начиная с которого удалить.\nПример: <code>purge 10</code>")
        n = 10
        if arg_tail.isdigit():
            n = max(1, min(int(arg_tail), 100))
        from_id    = msg.reply_to_message.message_id
        to_id      = msg.message_id
        ids_to_del = list(range(from_id, min(from_id + n, to_id + 1)))
        deleted = 0
        for i in range(0, len(ids_to_del), 100):
            batch = ids_to_del[i:i + 100]
            try:
                await bot.delete_messages(chat_id, batch)
                deleted += len(batch)
            except Exception:
                for mid in batch:
                    try:
                        await bot.delete_message(chat_id, mid)
                        deleted += 1
                    except Exception:
                        pass
        notice = await bot.send_message(chat_id, f"🧹 Удалено <b>{deleted}</b> сообщений.")
        await asyncio.sleep(4)
        try:
            await notice.delete()
        except Exception:
            pass
        return

    if cmd == "лимит":
        if not msg.reply_to_message:
            return await msg.reply("❌ Reply на сообщение пользователя.")
        target = msg.reply_to_message.from_user
        if not target:
            return await msg.reply("❌ Не определить пользователя.")
        if await is_chat_admin(bot, chat_id, target.id):
            return await msg.reply("🛡 Нельзя ограничивать админа!")
        secs, label = parse_time(arg_tail)
        if secs is None or secs == _FOREVER_SECS:
            return await msg.reply(
                f"❌ Не распознаю время: <code>{esc(arg_tail[:30])}</code>\n"
                "Пример: <code>лимит 30с</code> (макс. 10 мин)"
            )
        if secs > MAX_RATE_LIMIT_SECS:
            return await msg.reply("⚠️ Максимум — <b>10 минут</b>.")
        st.rate_intervals[target.id] = secs
        st.rate_last[target.id]      = 0.0
        await db_log("RATE_LIMIT", uid, target.id, chat_id, f"Лимит {label}")
        return await msg.reply(f"⏱ {mention(target)} — лимит <b>{label}</b> между сообщениями.")

    if cmd == "снять":
        if not msg.reply_to_message:
            return await msg.reply("❌ Reply на сообщение пользователя.")
        target = msg.reply_to_message.from_user
        if not target:
            return await msg.reply("❌ Не определить пользователя.")
        if target.id in st.rate_intervals:
            del st.rate_intervals[target.id]
            st.rate_last.pop(target.id, None)
            await db_log("REMOVE_LIMIT", uid, target.id, chat_id, "Снят лимит")
            return await msg.reply(f"✅ Лимит с {mention(target)} снят!")
        return await msg.reply(f"ℹ️ У {mention(target)} нет активного лимита.")

    if cmd in ("размут", "разбан", "разбан здесь", "размут здесь") and arg_tail and not msg.reply_to_message:
        raw  = arg_tail.split()[0]
        user = await resolve_user(bot, chat_id, raw)
        tid  = user.id if user else (
            int(raw.lstrip("@")) if raw.lstrip("@").lstrip("-").isdigit() else None
        )
        if not tid:
            return await msg.reply(f"❌ Не найден: <code>{esc(raw)}</code>")
        if cmd == "размут здесь":
            await unmute_user(bot, chat_id, tid)
            st.local_immune.add((chat_id, tid))
            await allow_twin_user(chat_id, tid, uid)
            await db_log("UNMUTE_LOCAL", uid, tid, chat_id, "По username/ID — иммунитет в чате")
            return await msg.reply(
                f"🔊 {mention(user) if user else f'<code>{tid}</code>'} размьючен в этом чате.\n"
                "🛡 <i>Иммунитет от авто-мута только здесь.</i>"
            )
        if cmd == "разбан здесь":
            await bot.unban_chat_member(chat_id, tid)
            st.banned_users[chat_id].discard(tid)
            st.ban_meta[chat_id].pop(tid, None)
            st.local_immune.add((chat_id, tid))
            await allow_twin_user(chat_id, tid, uid)
            await db_log("UNBAN_LOCAL", uid, tid, chat_id, "По username/ID — иммунитет в чате")
            return await msg.reply(
                f"✅ {mention(user) if user else f'<code>{tid}</code>'} разбанен в этом чате.\n"
                "🛡 <i>Иммунитет от авто-бана только здесь.</i>"
            )
        if cmd == "размут":
            await unmute_user(bot, chat_id, tid)
            await allow_twin_user(chat_id, tid, uid)
            await db_log("UNMUTE", uid, tid, chat_id, "По username/ID")
            return await msg.reply(f"🔊 {mention(user) if user else f'<code>{tid}</code>'} размьючен!")
        else:
            await bot.unban_chat_member(chat_id, tid)
            st.banned_users[chat_id].discard(tid)
            await allow_twin_user(chat_id, tid, uid)
            await db_log("UNBAN", uid, tid, chat_id, "По username/ID")
            return await msg.reply(f"✅ {mention(user) if user else f'<code>{tid}</code>'} разбанен!")

    if not msg.reply_to_message:
        if cmd in ("мут", "бан", "варн", "сброс", "варны"):
            return await msg.reply(
                "❌ Для этой команды нужен reply на сообщение пользователя.\n"
                "Примеры:\n"
                "• <code>мут 1ч причина</code>\n"
                "• <code>бан причина</code>\n"
                "• <code>варн причина</code>"
            )
        return await msg.reply(
            "❌ Нужен reply!\nИли: <code>разбан @username</code> / <code>размут ID</code>"
        )

    reply_msg = msg.reply_to_message
    target    = reply_msg.from_user

    if target and target.is_bot:
        bot_uid = extract_uid_from_bot_msg(reply_msg)
        if bot_uid:
            await _handle_bot_reply_cmd(msg, cmd, chat_id, uid, bot_uid)
        else:
            await msg.reply("❌ Не могу определить пользователя из сообщения бота.")
        return

    if not target:
        sc = getattr(reply_msg, "sender_chat", None)
        if sc:
            return await msg.reply(f"❌ Это канал: <b>{esc(sc.title)}</b>")
        return await msg.reply("❌ Не удалось определить пользователя.")

    target_is_admin = await is_chat_admin(bot, chat_id, target.id)

    if cmd == "варн":
        if target_is_admin:
            return await msg.reply("🛡 Нельзя варнить админа!")
        reason = parse_reason(arg_tail) if arg_tail else "не указана"
        count  = await db_warns_add(chat_id, target.id, reason, uid)
        await db_log("WARN", uid, target.id, chat_id, f"#{count}: {reason}")
        r_line = f"\n📝 Причина: <i>{esc(reason)}</i>"
        if count == 1:
            return await msg.reply(f"⚠️ {mention(target)} — предупреждение!{r_line}\n📊 <b>1/3</b>")
        if count == 2:
            await mute_user(bot, chat_id, target.id, 3600)
            await notify_auto_action(
                bot=bot,
                chat_id=chat_id,
                chat_title=msg.chat.title or "Группа",
                target_id=target.id,
                target_name=target.first_name or str(target.id),
                action="🔇 Мут (2-й варн)",
                reason=f"2-й варн: {reason}",
                duration="1 час",
            )
            return await msg.reply(
                f"🔇 {mention(target)} — 2-е предупреждение → мут <b>1 час</b>.{r_line}\n📊 <b>2/3</b>" + APPEAL_HINT
            )
        await bot.ban_chat_member(chat_id, target.id)
        st.banned_users[chat_id].add(target.id)
        st.ban_meta[chat_id][target.id] = {"reason": f"3 варна: {reason}", "ts": time.time(), "mod_id": uid}
        remember_recent_punishment(chat_id, target.id, "ban")
        await db_warns_reset(chat_id, target.id)
        await notify_auto_action(
            bot=bot,
            chat_id=chat_id,
            chat_title=msg.chat.title or "Группа",
            target_id=target.id,
            target_name=target.first_name or str(target.id),
            action="🚫 Бан (3 варна)",
            reason=f"3-й варн: {reason}",
            duration="",
        )
        return await msg.reply(f"🚫 {mention(target)} — <b>бан</b> (3 предупреждения).{r_line}" + APPEAL_HINT)

    if cmd == "сброс":
        await db_warns_reset(chat_id, target.id)
        await db_log("UNWARN", uid, target.id, chat_id, "Сброс варнов")
        return await msg.reply(f"♻️ Варны {mention(target)} сброшены!")

    if cmd == "варны":
        count = await db_warns_get(chat_id, target.id)
        return await msg.reply(f"📊 Варны {mention(target)}: <b>{count}/3</b>")

    if cmd == "мут":
        if target_is_admin:
            return await msg.reply("🛡 Нельзя мутить админа!")
        secs, label = parse_time(arg_tail)
        if secs is None:
            return await msg.reply(
                f"❌ Не распознаю время: <code>{esc(arg_tail[:30])}</code>\n"
                "Примеры: <code>мут 1ч</code>, <code>мут 30мин причина</code>, <code>мут навсегда</code>"
            )
        # Убираем временну́ю часть из хвоста чтобы получить только причину
        is_forever = (secs == _FOREVER_SECS)
        if is_forever:
            reason_raw = _RE_FOREVER.sub("", arg_tail).strip()
        else:
            reason_raw = _RE_TIME_FULL.sub("", arg_tail, count=1).strip()
        reason = parse_reason(reason_raw) if reason_raw else ""
        r_line = f"\n📝 Причина: <i>{esc(reason)}</i>" if reason else ""
        # _FOREVER_SECS=-1 → передаём None в mute_user (бессрочный мут)
        await mute_user(bot, chat_id, target.id, None if is_forever else secs, reason=reason, mod_id=uid)
        await safe_delete(reply_msg)
        await db_log("MUTE", uid, target.id, chat_id, f"{label} {reason}")
        # Сохраняем хэш сообщения нарушителя для авто-детектора твинков
        if reply_msg and (reply_msg.text or reply_msg.caption):
            _rh = _text_hash((reply_msg.text or reply_msg.caption or "").strip())
            if len((reply_msg.text or reply_msg.caption or "")) >= TWIN_MIN_LEN:
                _remember_text_hash(chat_id, _rh, target.id, False)
        return await msg.reply(
            f"🔇 {mention(target)} — мут <b>{label}</b>.{r_line}\n<code>uid:{target.id}</code>" + APPEAL_HINT
        )

    if cmd == "размут":
        await unmute_user(bot, chat_id, target.id)
        await allow_twin_user(chat_id, target.id, uid)
        await db_log("UNMUTE", uid, target.id, chat_id, "Снят мут")
        return await msg.reply(f"🔊 {mention(target)} размьючен!")

    if cmd == "бан":
        if target_is_admin:
            return await msg.reply("🛡 Нельзя банить админа!")
        secs, label = parse_time(arg_tail)
        reason_raw  = _RE_TIME_FULL.sub("", arg_tail, count=1).strip() if arg_tail else ""
        reason      = parse_reason(reason_raw) if reason_raw else ""
        r_line      = f"\n📝 Причина: <i>{esc(reason)}</i>" if reason else ""
        if secs:
            await bot.ban_chat_member(
                chat_id, target.id,
                until_date=datetime.now(timezone.utc) + timedelta(seconds=secs),
            )
            remember_recent_punishment(chat_id, target.id, "ban")
            await db_log("BAN_TEMP", uid, target.id, chat_id, f"{label} {reason}")
            txt = f"🚫 {mention(target)} — бан <b>{label}</b>.{r_line}"
        else:
            await bot.ban_chat_member(chat_id, target.id)
            st.banned_users[chat_id].add(target.id)
            st.ban_meta[chat_id][target.id] = {"reason": reason or "—", "ts": time.time(), "mod_id": uid}
            remember_recent_punishment(chat_id, target.id, "ban")
            # Явный бан снимает иммунитет «разбан здесь»
            st.local_immune.discard((chat_id, target.id))
            await db_log("BAN_PERM", uid, target.id, chat_id, reason)
            txt = f"🚫 {mention(target)} — <b>перм-бан</b>.{r_line}"
        await safe_delete(reply_msg)
        # Сохраняем хэш сообщения нарушителя для авто-детектора твинков
        if reply_msg and (reply_msg.text or reply_msg.caption):
            _rh = _text_hash((reply_msg.text or reply_msg.caption or "").strip())
            if len((reply_msg.text or reply_msg.caption or "")) >= TWIN_MIN_LEN:
                _remember_text_hash(chat_id, _rh, target.id, True)
        return await msg.reply(f"{txt}\n<code>uid:{target.id}</code>" + APPEAL_HINT)

    if cmd in ("снять_мат", "unmute_mat", "mat_off", "снять мат"):
        if not target:
            return await msg.reply("❌ Нужен reply на сообщение пользователя.")
        st.mat_silent_users.discard((chat_id, target.id))
        await db_log("MAT_SILENT_OFF", uid, target.id, chat_id, "Тихий режим снят")
        return await msg.reply(
            f"✅ Тихий режим снят для {mention(target)}\n"
            "Следующее матерное — снова форвард модераторам."
        )

    if cmd in ("разбан здесь", "размут здесь"):
        if not target:
            return await msg.reply("❌ Нужен reply на сообщение пользователя.")
        if cmd == "разбан здесь":
            try:
                await bot.unban_chat_member(chat_id, target.id)
            except Exception as _e:
                log.warning("разбан здесь: %s", _e)
            st.banned_users[chat_id].discard(target.id)
            st.ban_meta[chat_id].pop(target.id, None)
            action_log = "UNBAN_LOCAL"
            reply_txt  = f"✅ {mention(target)} разбанен в этом чате."
        else:
            try:
                await unmute_user(bot, chat_id, target.id)
            except Exception as _e:
                log.warning("размут здесь: %s", _e)
            action_log = "UNMUTE_LOCAL"
            reply_txt  = f"🔊 {mention(target)} размьючен в этом чате."
        st.local_immune.add((chat_id, target.id))
        await allow_twin_user(chat_id, target.id, uid)
        await db_log(action_log, uid, target.id, chat_id, "Иммунитет в этом чате")
        return await msg.reply(
            reply_txt + "\n"
            "🛡 <i>Иммунитет от авто-бана/мута только в этом чате.</i>\n"
            "<i>Чтобы забанить снова — используй обычный</i> <code>бан</code>."
        )

    if cmd == "разбан":
        await bot.unban_chat_member(chat_id, target.id)
        st.banned_users[chat_id].discard(target.id)
        st.ban_meta[chat_id].pop(target.id, None)
        await allow_twin_user(chat_id, target.id, uid)
        await db_log("UNBAN", uid, target.id, chat_id, "Разбан")
        return await msg.reply(f"✅ {mention(target)} разбанен!")


async def _handle_bot_reply_cmd(
    msg: Message, cmd: str, chat_id: int, mod_id: int, target_id: int
) -> None:
    if cmd == "размут":
        await unmute_user(bot, chat_id, target_id)
        await allow_twin_user(chat_id, target_id, mod_id)
        await db_log("UNMUTE", mod_id, target_id, chat_id, "Reply на бота")
        await msg.reply(f"🔊 <code>{target_id}</code> размьючен!")
    elif cmd == "разбан":
        await bot.unban_chat_member(chat_id, target_id)
        st.banned_users[chat_id].discard(target_id)
        st.ban_meta[chat_id].pop(target_id, None)
        await allow_twin_user(chat_id, target_id, mod_id)
        await db_log("UNBAN", mod_id, target_id, chat_id, "Reply на бота")
        await msg.reply(f"✅ <code>{target_id}</code> разбанен!")
    elif cmd == "сброс":
        await db_warns_reset(chat_id, target_id)
        await db_log("UNWARN", mod_id, target_id, chat_id, "Reply на бота")
        await msg.reply(f"♻️ Варны <code>{target_id}</code> сброшены!")
    elif cmd == "варны":
        count = await db_warns_get(chat_id, target_id)
        await msg.reply(f"📊 Варны <code>{target_id}</code>: <b>{count}/3</b>")
    else:
        await msg.reply("❌ Эта команда требует прямого reply на пользователя.")


# ─────────────────────────────────────────────────────────
# ФОНОВЫЕ ЗАДАЧИ
# ─────────────────────────────────────────────────────────

async def task_db_ping() -> None:
    while True:
        await asyncio.sleep(300)
        try:
            async with st.pool.acquire() as c:
                await c.fetchval("SELECT 1")
            log.debug("DB ping OK")
        except Exception as e:
            log.warning("DB ping failed: %s", e)


async def task_birthday() -> None:
    MSK        = timezone(timedelta(hours=3))
    sent_today = False
    while True:
        now = datetime.now(MSK)
        if now.month == 6 and now.day == 10 and not sent_today:
            try:
                await bot.send_message(BIRTHDAY_CHAT_ID, "🎂 @Timmy_Falcon, с Днём Рождения! 🥳🎉")
                log.info("ДР поздравление отправлено")
            except Exception as e:
                log.error("ДР ошибка: %s", e)
            sent_today = True
        elif now.day != 10:
            sent_today = False
        await asyncio.sleep(3600)


async def task_clean_flood() -> None:
    while True:
        await asyncio.sleep(600)
        try:
            now_ts = time.monotonic()
            expired_start = [uid for uid, ts in _start_flood.items() if now_ts - ts > START_FLOOD_INTERVAL * 2]
            for uid in expired_start:
                _start_flood.pop(uid, None)
            # Очищаем старые action_taken (держим не более 2000 записей)
            if len(st.action_taken) > 2000:
                keys = list(st.action_taken.keys())
                for k in keys[:500]:
                    del st.action_taken[k]
            # Чистим мелкие TTL-кэши
            now_ts_m = time.monotonic()
            st.chat_admin_cache = {k: v for k, v in st.chat_admin_cache.items() if now_ts_m - v[0] <= 60}
            st.role_name_cache  = {k: v for k, v in st.role_name_cache.items()  if now_ts_m - v[0] <= 120}
            # Чистим старые pending_auto_mutes (старше 48 часов)
            now_ts_s = time.time()
            old_pending = [nid for nid, v in st.pending_auto_mutes.items() if now_ts_s - v["ts"] > 172800]
            for nid in old_pending:
                st.pending_auto_mutes.pop(nid, None)
                st.notif_hash.pop(nid, None)
            # Чистим deal_* словари (старше 24 часов — сделки должны завершаться быстро)
            deal_cutoff = now_ts_s - 86400
            stale_deals = [did for did, status in st.deal_status.items() if status in ("link_sent", "declined") and True]
            # Ограничиваем размер deal-словарей
            if len(st.deal_status) > 500:
                old_deals = list(st.deal_status.keys())[:200]
                for did in old_deals:
                    st.deal_status.pop(did, None)
                    st.deal_links.pop(did, None)
                    st.deal_participants.pop(did, None)
                    st.deal_origin_message.pop(did, None)
                    st.deal_uids.pop(did, None)
                    st.accepted_deals.pop(did, None)
                    st.garant_pending_deal = {k: v for k, v in st.garant_pending_deal.items() if v not in old_deals}
            # Чистим hash_pardons (ограничиваем размер)
            if len(st.hash_pardons) > 5000:
                items_p = list(st.hash_pardons)
                st.hash_pardons = set(items_p[-3000:])
            # Чистим старые mat_pending (старше 48ч — решение уже не будет принято)
            _now = time.time()
            old_mat = [k for k, v in st.mat_pending.items() if _now - v.get("ts", 0) > 172800]
            for k in old_mat:
                st.mat_pending.pop(k, None)
            # Чистим старые doxx_pending (старше 48ч — решение уже не будет принято)
            old_doxx = [k for k, v in st.doxx_pending.items() if _now - v.get("ts", 0) > 172800]
            for k in old_doxx:
                st.doxx_pending.pop(k, None)
                st.notif_hash.pop(k, None)
            # mat_silent_users не чистим — решение постоянное пока не снято вручную
            if expired_start:
                log.debug("Очищено %d записей антифлуда /start", len(expired_start))
        except Exception as e:
            log.warning("task_clean_flood failed: %s", e)


async def task_db_cleanup() -> None:
    # Раз в сутки удаляем старые записи логов, чтобы БД не росла бесконечно
    while True:
        await asyncio.sleep(24 * 3600)
        cutoff = datetime.now(timezone.utc) - timedelta(days=DB_LOG_RETENTION_DAYS)
        try:
            # LIMIT чтобы не блочить БД надолго при большом накопленном объёме
            async with st.pool.acquire() as c:
                r1 = await c.execute(
                    "DELETE FROM action_logs WHERE id IN "
                    "(SELECT id FROM action_logs WHERE ts < $1 LIMIT 2000)", cutoff,
                )
                r2 = await c.execute(
                    "DELETE FROM warn_history WHERE id IN "
                    "(SELECT id FROM warn_history WHERE ts < $1 LIMIT 2000)", cutoff,
                )
                r3 = await c.execute(
                    "DELETE FROM appeals WHERE id IN "
                    "(SELECT id FROM appeals WHERE created_at < $1 AND status != 'open' LIMIT 500)",
                    cutoff,
                )
            log.info("DB cleanup: %s / %s / %s (retention %d дней)", r1, r2, r3, DB_LOG_RETENTION_DAYS)
        except Exception as e:
            log.warning("DB cleanup failed: %s", e)


async def health(_: web.Request) -> web.Response:
    return web.Response(text="OK")


async def start_web() -> None:
    app = web.Application()
    app.router.add_get("/", health)
    runner = web.AppRunner(app)
    await runner.setup()
    await web.TCPSite(runner, "0.0.0.0", PORT).start()
    log.info("Web server on port %d", PORT)


async def _supervised(name: str, coro_func) -> None:
    """Гарантирует, что фоновая задача не умрёт навсегда: если корутина всё же
    вылетела с исключением наружу (несмотря на try/except внутри неё), логируем
    и перезапускаем через паузу, а не теряем задачу до перезапуска бота."""
    while True:
        try:
            await coro_func()
        except asyncio.CancelledError:
            raise
        except Exception as e:
            log.error("Фоновая задача %s упала, перезапуск через 30с: %s", name, e)
            await asyncio.sleep(30)
        else:
            # Функция не должна была завершиться (там while True) — на всякий случай тоже рестартуем
            log.error("Фоновая задача %s неожиданно завершилась, перезапуск через 30с", name)
            await asyncio.sleep(30)


async def main() -> None:
    global BOT_USERNAME
    await db_init()
    await start_web()
    me = await bot.get_me()
    BOT_USERNAME = me.username or ""
    log.info("Bot @%s started", me.username)
    asyncio.create_task(_supervised("task_db_ping", task_db_ping))
    asyncio.create_task(_supervised("task_birthday", task_birthday))
    asyncio.create_task(_supervised("task_clean_flood", task_clean_flood))
    asyncio.create_task(_supervised("task_db_cleanup", task_db_cleanup))
    await dp.start_polling(
        bot,
        allowed_updates=["message", "callback_query"],
        drop_pending_updates=True,
    )


if __name__ == "__main__":
    asyncio.run(main())
