"""Hệ thống cập nhật tin tài chính - giai đoạn 1.

Cách chạy:
  python tin_tuc.py           lấy tin mới, lưu vào tin_tuc.db, gửi Telegram
  python tin_tuc.py --thu     chạy thử: lấy tin và in ra màn hình, không lưu, không gửi
  python tin_tuc.py --setup   lấy chat_id sau khi đã dán token vào bi_mat.ini và nhắn cho bot

Chạy trên máy (Task Scheduler) hoặc trên GitHub Actions (.github/workflows/tin_tuc.yml).
"""
import argparse
import configparser
import csv
import hashlib
import html
import json
import logging
import os
import re
import sqlite3
import sys
import unicodedata
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from logging.handlers import RotatingFileHandler
from pathlib import Path
from urllib.parse import quote_plus

import feedparser
import requests

THU_MUC = Path(__file__).resolve().parent
CONFIG = THU_MUC / "config.ini"
FILE_BI_MAT = THU_MUC / "bi_mat.ini"
DB = THU_MUC / "tin_tuc.db"
FILE_MA = THU_MUC / "ma_hose.csv"
FILE_TEN = THU_MUC / "ten_goi_khac.csv"
FILE_TEMPLATE = THU_MUC / "tin_tuc_template.html"
FILE_HTML = THU_MUC / "tin_tuc.html"
NGAY_HTML = 3          # trang HTML hiện tin trong bấy nhiêu ngày
UA = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                    "(KHTML, like Gecko) Chrome/126.0 Safari/537.36"}
VN_TZ = timezone(timedelta(hours=7))

LUU_TOI_DA_GIO = 48    # bỏ qua tin cũ hơn mức này
XOA_SAU_NGAY = 30      # kho tin chỉ giữ bấy nhiêu ngày cho gọn
DICH_TOI_DA_MOI_LAN = 40   # tin tồn đọng nhiều thì dịch dần qua các lần chạy
GUI_TOI_DA_GIO = 12    # tin chưa gửi mà cũ hơn mức này thì không gửi nữa (sau khi máy tắt lâu)

GN_EN = "https://news.google.com/rss/search?hl=en-US&gl=US&ceid=US:en&q="
GN_VI = "https://news.google.com/rss/search?hl=vi&gl=VN&ceid=VN:vi&q="
# Google News chỉ lấy từ các báo này, tránh tin rác từ trang nhỏ
BAO_EN = "site:reuters.com OR site:bloomberg.com OR site:cnbc.com OR site:wsj.com OR site:ft.com OR site:kitco.com OR site:oilprice.com"
BAO_VI = "site:vneconomy.vn OR site:vietnambiz.vn OR site:thoibaonganhang.vn OR site:baochinhphu.vn OR site:sbv.gov.vn OR site:bnews.vn"

# (tên nguồn, url, nhóm, lọc). lọc=True: chỉ giữ tin có mã CK hoặc từ khóa quan trọng
NGUON = [
    ("CafeF", "https://cafef.vn/thi-truong-chung-khoan.rss", "ck", False),
    ("CafeF", "https://cafef.vn/doanh-nghiep.rss", "dn", True),
    ("CafeF", "https://cafef.vn/vi-mo-dau-tu.rss", "vm", True),
    ("CafeF", "https://cafef.vn/tai-chinh-ngan-hang.rss", "vm", False),
    ("CafeF", "https://cafef.vn/thi-truong.rss", "hh", True),
    ("CafeF", "https://cafef.vn/tai-chinh-quoc-te.rss", "qt", True),
    ("Vietstock", "https://vietstock.vn/830/chung-khoan/co-phieu.rss", "ck", False),
    ("Vietstock", "https://vietstock.vn/737/doanh-nghiep/hoat-dong-kinh-doanh.rss", "dn", False),
    ("Vietstock", "https://vietstock.vn/738/doanh-nghiep/co-tuc.rss", "dn", False),
    ("Vietstock", "https://vietstock.vn/739/chung-khoan/giao-dich-noi-bo.rss", "dn", False),
    ("Vietstock", "https://vietstock.vn/741/chung-khoan/niem-yet.rss", "dn", False),
    ("Vietstock", "https://vietstock.vn/764/doanh-nghiep/tang-von-m-a.rss", "dn", False),
    ("Vietstock", "https://vietstock.vn/145/chung-khoan/y-kien-chuyen-gia.rss", "cg", False),
    ("Vietstock", "https://vietstock.vn/1636/nhan-dinh-phan-tich/nhan-dinh-thi-truong.rss", "cg", False),
    ("Vietstock", "https://vietstock.vn/582/nhan-dinh-phan-tich/phan-tich-co-ban.rss", "cg", False),
    ("Vietstock", "https://vietstock.vn/143/chung-khoan/chinh-sach.rss", "vm", False),
    ("Vietstock", "https://vietstock.vn/761/kinh-te/vi-mo.rss", "vm", False),
    ("Vietstock", "https://vietstock.vn/757/tai-chinh/ngan-hang.rss", "vm", False),
    ("Vietstock", "https://vietstock.vn/2/hang-hoa.rss", "hh", False),
    ("Vietstock", "https://vietstock.vn/773/the-gioi/chung-khoan-the-gioi.rss", "qt", False),
    ("Vietstock", "https://vietstock.vn/772/the-gioi/tai-chinh-quoc-te.rss", "qt", False),
    ("TNCK", "https://tinnhanhchungkhoan.vn/rss/chung-khoan-2.rss", "ck", False),
    ("VnExpress", "https://vnexpress.net/rss/kinh-doanh.rss", "vm", True),
    ("Tuổi Trẻ", "https://tuoitre.vn/rss/kinh-doanh.rss", "vm", True),
    ("Thanh Niên", "https://thanhnien.vn/rss/kinh-te.rss", "vm", True),
    ("Google News", GN_VI + quote_plus(f'("Ngân hàng Nhà nước" OR "lãi suất" OR "tỷ giá" OR "chứng khoán") ({BAO_VI}) when:2d'), "vm", True),
    ("Fed", "https://www.federalreserve.gov/feeds/press_all.xml", "qt", True),
    ("CNBC", "https://www.cnbc.com/id/100003114/device/rss/rss.html", "qt", True),
    ("CNBC", "https://www.cnbc.com/id/10000664/device/rss/rss.html", "qt", True),
    ("MarketWatch", "https://feeds.content.dowjones.io/public/rss/mw_topstories", "qt", True),
    ("Google News", GN_EN + quote_plus(f'("Federal Reserve" OR FOMC OR "oil prices" OR "gold prices" OR "copper prices" OR Vietnam) ({BAO_EN}) when:1d'), "qt", False),
]

TEN_NHOM = {
    "dn": "🏢 Doanh nghiệp",
    "ck": "📈 Thị trường chứng khoán",
    "cg": "🗣 Nhận định - chuyên gia",
    "vm": "🏦 Vĩ mô - Tiền tệ",
    "hh": "🛢 Hàng hóa",
    "qt": "🌍 Quốc tế",
}

TU_KHOA_VN = [
    "lãi suất", "tỷ giá", "ngân hàng nhà nước", "nhnn", "lạm phát", "cpi", "gdp", "tín dụng",
    "fed", "trái phiếu", "giá vàng", "vàng miếng", "giá dầu", "xăng dầu", "giá thép", "phân bón",
    "cao su", "cà phê", "giá gạo", "đầu tư công", "fdi", "xuất khẩu", "thuế quan", "chứng khoán",
    "vn-index", "vnindex", "khối ngoại", "nâng hạng", "margin", "cổ phiếu", "cổ tức",
    "lợi nhuận", "doanh thu", "lãi ròng", "kqkd", "kết quả kinh doanh", "niêm yết", "thoái vốn", "sáp nhập",
    "m&a", "ipo", "cổ đông", "đhđcđ", "tăng vốn", "phát hành", "giá điện",
]

# Phân loại theo nội dung tiêu đề (chuyên mục của báo chỉ là gợi ý ban đầu)
RE_HANG_HOA = re.compile(
    r"giá (vàng|bạc|dầu|xăng|thép|tôn|cà phê|cao su|gạo|lúa|hồ tiêu|tiêu|heo|lợn|phân bón|than|quặng|đường|điều|"
    r"sầu riêng|nông sản)|vàng (miếng|nhẫn|sjc)", re.I)
# Bài bảng giá, lãi suất hằng ngày: nhắc tên nhiều ngân hàng, tiệm vàng nhưng không phải tin doanh nghiệp
RE_TONG_HOP = re.compile(r"^(giá|lãi suất|tỷ giá|biểu lãi suất)\b.*(ngày|hôm nay|sáng|chiều|\d{1,2}/\d{1,2})", re.I)
RE_NGU_CANH_MA = r"(?i:\(|mã\s+|cổ phiếu\s+|cp\s+|hose:\s*|hsx:\s*){m}(?![{chu}])"
TU_KHOA_EN = re.compile(
    r"\b(fed|federal reserve|fomc|powell|interest rates?|rate cut|rate hike|inflation|cpi|"
    r"treasur(y|ies)|bond yields?|oil|crude|opec|gold|copper|steel|iron ore|dollar|tariffs?|"
    r"china|vietnam|emerging markets?|s&p 500|nasdaq|dow|recession|payrolls?|jobs report)\b",
    re.I,
)

# Mã trùng với từ viết tắt thông dụng: chỉ nhận khi có "mã X", "cổ phiếu X", "(X)", "HOSE: X"
MA_DE_NHAM = {"VND", "HCM", "SBV", "SSC", "VIP", "COM", "GAS", "PET", "FIT", "ECO", "ICT",
              "VNG", "VPS", "SGN", "TCT", "NAV", "SMA", "ABS", "CCC"}
CHU = "A-Za-z0-9À-ỹ"
RE_MA = re.compile(rf"(?<![{CHU}])([A-Z][A-Z0-9]{{2}})(?![{CHU}])")

log = logging.getLogger("tin_tuc")


def cai_log():
    log.setLevel(logging.INFO)
    fh = RotatingFileHandler(THU_MUC / "tin_tuc.log", maxBytes=1_000_000, backupCount=2, encoding="utf-8")
    fh.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
    log.addHandler(fh)
    if sys.stdout:  # chạy bằng pythonw (ẩn cửa sổ) thì không có stdout
        log.addHandler(logging.StreamHandler(sys.stdout))


def doc_config():
    """config.ini (cài đặt, đưa lên GitHub được) + bi_mat.ini (token, chỉ nằm trên máy).
    Trên GitHub, token lấy từ biến môi trường TELEGRAM_TOKEN / TELEGRAM_CHAT_ID (GitHub Secrets)."""
    cfg = configparser.ConfigParser()
    cfg.read([CONFIG, FILE_BI_MAT], encoding="utf-8")
    if not cfg.has_section("telegram"):
        cfg.add_section("telegram")
    for khoa, bien in (("token", "TELEGRAM_TOKEN"), ("chat_id", "TELEGRAM_CHAT_ID")):
        if os.environ.get(bien):
            cfg.set("telegram", khoa, os.environ[bien].strip())
    return cfg


def doc_ma():
    with open(FILE_MA, encoding="utf-8") as f:
        return {r["ma"].strip().upper() for r in csv.DictReader(f)}


def doc_ten_goi():
    """Tên công ty hay xuất hiện trong bài báo -> mã, đọc từ ten_goi_khac.csv (bạn tự thêm được)."""
    if not FILE_TEN.exists():
        return []
    with open(FILE_TEN, encoding="utf-8") as f:
        return [(re.compile(rf"(?<![{CHU}]){re.escape(r['ten'].strip())}(?![{CHU}])", re.I),
                 r["ma"].strip().upper()) for r in csv.DictReader(f) if r["ten"].strip()]


def bo_dau(s):
    s = unicodedata.normalize("NFD", s.lower()).replace("đ", "d")
    s = "".join(c for c in s if unicodedata.category(c) != "Mn")
    return re.sub(r"[^a-z0-9]+", " ", s).strip()


def lam_sach(s):
    s = re.sub(r"<[^>]+>", " ", s or "")
    return re.sub(r"\s+", " ", html.unescape(s)).strip()


def tim_ma(text, tat_ca_ma, ten_goi):
    ma = [m for re_ten, m in ten_goi if re_ten.search(text)]
    ma = list(dict.fromkeys(ma))
    for m in RE_MA.findall(text):
        if m not in tat_ca_ma or m in ma:
            continue
        if m in MA_DE_NHAM and not co_ngu_canh_ma(m, text):
            continue
        ma.append(m)
    return ma


def co_ngu_canh_ma(m, text):
    """Có "mã X", "cổ phiếu X", "(X)", "HOSE: X" trong bài: chắc chắn đang nói về cổ phiếu X."""
    return bool(re.search(RE_NGU_CANH_MA.format(m=m, chu=CHU), text))


def phan_loai(tieu_de, tom_tat, nhom_nguon, loc, tieng_viet, tat_ca_ma, ten_goi):
    """Nhóm tin, mã CK và có giữ tin không, dựa vào nội dung; nhom_nguon là chuyên mục của báo.
    - Tiêu đề về giá hàng hóa (giá vàng, giá xăng...) -> Hàng hóa.
    - Tin vĩ mô mà tiêu đề nói về 1-2 doanh nghiệp niêm yết (vd "Vietcombank trích lập...") -> Doanh nghiệp.
    - Bài bảng giá/lãi suất hằng ngày và bài hàng hóa: chỉ gắn mã khi bài nói rõ về cổ phiếu
      (tránh gắn PNJ vì "giá vàng tại PNJ", gắn 7 ngân hàng vì bảng lãi suất)."""
    noi_dung = f"{tieu_de} {tom_tat}"
    if not tieng_viet:
        return nhom_nguon, [], bool(TU_KHOA_EN.search(noi_dung)) if loc else True
    ma = tim_ma(noi_dung, tat_ca_ma, ten_goi) if nhom_nguon != "qt" else []
    tong_hop = bool(RE_TONG_HOP.search(tieu_de))
    nhom = nhom_nguon
    if nhom_nguon != "qt" and RE_HANG_HOA.search(tieu_de):
        nhom = "hh"
    elif nhom_nguon == "vm" and not tong_hop:
        ma_td = [m for m in ma if m in tim_ma(tieu_de, tat_ca_ma, ten_goi)]
        if 1 <= len(ma_td) <= 2:
            nhom = "dn"
    elif nhom_nguon == "dn" and not ma:
        nhom = "vm"   # chuyên mục Doanh nghiệp nhưng không gắn được công ty niêm yết nào: tin kinh tế chung
    if tong_hop or nhom == "hh":
        ma = [m for m in ma if co_ngu_canh_ma(m, noi_dung)]
    giu = (bool(ma) or any(k in noi_dung.lower() for k in TU_KHOA_VN)) if loc else True
    return nhom, ma, giu


def doc_ngay(e):
    """Ngày đăng (UTC). Không đọc được ngày thì trả None để bỏ tin, tránh tin cũ bị coi là mới."""
    t = e.get("published_parsed") or e.get("updated_parsed")
    if t:
        return datetime(*t[:6], tzinfo=timezone.utc)
    s = e.get("published") or e.get("updated")
    if not s:
        return None
    try:
        # Một số báo ghi múi giờ "+07" thay vì "+0700"
        d = parsedate_to_datetime(re.sub(r"([+-]\d{2})$", r"\g<1>00", s.strip()))
        return d.astimezone(timezone.utc) if d.tzinfo else d.replace(tzinfo=VN_TZ).astimezone(timezone.utc)
    except (TypeError, ValueError):
        return None


def lay_nguon(nguon):
    ten, url, nhom, loc = nguon
    try:
        r = requests.get(url, headers=UA, timeout=20)
        r.raise_for_status()
        return nguon, feedparser.parse(r.content).entries
    except Exception as e:
        log.warning("Lỗi nguồn %s %s: %s", ten, url, e)
        return nguon, []


def thu_thap(tat_ca_ma):
    """Đọc tất cả nguồn, trả về danh sách tin đã gắn mã và đánh dấu giữ/bỏ."""
    ten_goi = doc_ten_goi()
    gioi_han = datetime.now(timezone.utc) - timedelta(hours=LUU_TOI_DA_GIO)
    tin = []
    with ThreadPoolExecutor(max_workers=8) as ex:
        ket_qua = list(ex.map(lay_nguon, NGUON))
    trong = sorted({f"{n[0]} ({n[1].split('/')[2]})" for n, entries in ket_qua if not entries})
    if trong:
        log.warning("Nguồn không lấy được tin: %s", ", ".join(trong))
    for (ten, url, nhom, loc), entries in ket_qua:
        for e in entries:
            tieu_de = lam_sach(e.get("title"))
            link = e.get("link", "")
            if not tieu_de or not link:
                continue
            nguon = ten
            if ten == "Google News":
                src = e.get("source", {}).get("title")
                if src:
                    nguon = src
                    tieu_de = re.sub(rf"\s+-\s+{re.escape(src)}$", "", tieu_de)
            thoi_gian = doc_ngay(e)
            if thoi_gian is None or thoi_gian < gioi_han:
                continue
            tom_tat = lam_sach(e.get("summary"))[:400]
            tieng_viet = ".vn/" in url or "hl=vi" in url
            nhom_tin, ma, giu = phan_loai(tieu_de, tom_tat, nhom, loc, tieng_viet, tat_ca_ma, ten_goi)
            tin.append({
                "id": hashlib.sha1(link.encode()).hexdigest(),
                "khoa_td": bo_dau(tieu_de),
                "nguon": nguon, "nhom": nhom_tin, "tieu_de": tieu_de, "link": link,
                "tom_tat": tom_tat, "ma": ",".join(ma),
                "thoi_gian": thoi_gian.isoformat(), "giu": int(giu),
                "nhom_nguon": nhom, "loc": int(loc), "tieng_viet": int(tieng_viet),
            })
    return tin


def mo_db():
    con = sqlite3.connect(DB)
    con.execute("""CREATE TABLE IF NOT EXISTS tin (
        id TEXT PRIMARY KEY, khoa_td TEXT, nguon TEXT, nhom TEXT, tieu_de TEXT, link TEXT,
        tom_tat TEXT, ma TEXT, thoi_gian TEXT, lay_luc TEXT, giu INTEGER, da_gui INTEGER DEFAULT 0)""")
    con.execute("CREATE INDEX IF NOT EXISTS ix_khoa ON tin(khoa_td)")
    con.execute("CREATE INDEX IF NOT EXISTS ix_ma ON tin(ma)")
    # dich: 0 = chưa xét, 1 = đã dịch sang tiếng Việt, 2 = tin tiếng Việt, không cần dịch
    cot = {r[1] for r in con.execute("PRAGMA table_info(tin)")}
    if "dich" not in cot:
        con.execute("ALTER TABLE tin ADD COLUMN dich INTEGER DEFAULT 0")
    # chuyên mục gốc của báo, có lọc không, nguồn tiếng Việt không: để phân loại lại khi đổi luật
    for ten in ("nhom_nguon", "loc", "tieng_viet"):
        if ten not in cot:
            con.execute(f"ALTER TABLE tin ADD COLUMN {ten}")
    con.execute("""CREATE TABLE IF NOT EXISTS bao_cao (
        link TEXT PRIMARY KEY, ma TEXT, ctck TEXT, ctck_ngan TEXT, tieu_de TEXT, loai TEXT, ngay TEXT,
        tom_tat TEXT, khuyen_nghi TEXT, gia_muc_tieu REAL, lay_luc TEXT, da_gui INTEGER DEFAULT 0)""")
    return con


def luu(con, tin):
    """Lưu tin mới, bỏ tin trùng link hoặc trùng tiêu đề (nhiều báo đăng lại). Trả về số tin mới."""
    moi = 0
    bay_gio = datetime.now(timezone.utc).isoformat()
    for t in tin:
        if con.execute("SELECT 1 FROM tin WHERE id=? OR khoa_td=?", (t["id"], t["khoa_td"])).fetchone():
            continue
        con.execute("INSERT INTO tin (id,khoa_td,nguon,nhom,tieu_de,link,tom_tat,ma,thoi_gian,lay_luc,giu,da_gui,dich,"
                    "nhom_nguon,loc,tieng_viet) VALUES (:id,:khoa_td,:nguon,:nhom,:tieu_de,:link,:tom_tat,:ma,:thoi_gian,"
                    ":lay_luc,:giu,0,0,:nhom_nguon,:loc,:tieng_viet)", {**t, "lay_luc": bay_gio})
        moi += 1
    con.commit()
    return moi


def phan_loai_lai(con, tat_ca_ma, ten_goi):
    """Áp luật phân loại hiện hành cho tin trong NGAY_HTML ngày gần nhất (trang HTML hiện đúng ngay khi đổi luật).
    Chỉ có thể bỏ tin (giu 1 -> 0), không bật lại tin đã bỏ."""
    han = (datetime.now(timezone.utc) - timedelta(days=NGAY_HTML)).isoformat()
    doi = 0
    for r in con.execute("SELECT * FROM tin WHERE giu=1 AND thoi_gian>=?", (han,)).fetchall():
        nhom_goc = r["nhom_nguon"] or r["nhom"]
        if r["tieng_viet"] is None:
            if r["nhom"] == "qt":   # tin cũ chưa ghi nguồn: không biết là báo Việt hay báo ngoại
                continue
            # tin cũ: chuyên mục Doanh nghiệp CafeF nay có lọc; các nguồn khác giữ như lúc lấy
            loc, tieng_viet = r["nguon"] == "CafeF" and nhom_goc == "dn", True
        else:
            loc, tieng_viet = bool(r["loc"]), bool(r["tieng_viet"])
            if not tieng_viet:   # tin báo ngoại: đã dịch nên không áp lại bộ lọc từ khóa tiếng Anh
                continue
        nhom, ma, giu = phan_loai(r["tieu_de"], r["tom_tat"] or "", nhom_goc, loc, tieng_viet, tat_ca_ma, ten_goi)
        ma = ",".join(ma)
        if (nhom, ma, int(giu)) != (r["nhom"], r["ma"], 1):
            con.execute("UPDATE tin SET nhom=?, ma=?, giu=?, nhom_nguon=? WHERE id=?",
                        (nhom, ma, int(giu), nhom_goc, r["id"]))
            doi += 1
    con.commit()
    if doi:
        log.info("Phân loại lại %d tin", doi)


def trong_gio_yen_lang(cfg):
    khoang = cfg.get("cai_dat", "gio_yen_lang", fallback="").strip()
    if not khoang:
        return False
    a, b = (int(x) for x in khoang.split("-"))
    h = datetime.now(VN_TZ).hour
    return a <= h < b if a < b else (h >= a or h < b)


def rut_gon_sapo(tom_tat, tieu_de, toi_da=220):
    """Sapo ngắn gọn để hiện dưới tiêu đề. Bỏ khi nguồn chỉ lặp lại tiêu đề (Google News, Fed)."""
    s = (tom_tat or "").strip()
    if bo_dau(s).startswith(bo_dau(tieu_de)):
        s = s[len(tieu_de):].strip()
    if len(s) < 40:
        return ""
    if len(s) > toi_da:
        s = s[:toi_da].rsplit(" ", 1)[0].rstrip(",.;:") + "…"
    return s


RE_TIENG_VIET = re.compile(r"[àáạảãâầấậẩẫăằắặẳẵèéẹẻẽêềếệểễìíịỉĩòóọỏõôồốộổỗơờớợởỡùúụủũưừứựửữỳýỵỷỹđ]", re.I)


def _dich_google(text):
    r = requests.get("https://translate.googleapis.com/translate_a/single", timeout=15, params={
        "client": "gtx", "sl": "auto", "tl": "vi", "dt": "t", "q": text})
    r.raise_for_status()
    return "".join(seg[0] for seg in r.json()[0] if seg[0])


def _dich_google_2(text):
    r = requests.get("https://clients5.google.com/translate_a/t", timeout=15, params={
        "client": "dict-chrome-ex", "sl": "auto", "tl": "vi", "q": text})
    r.raise_for_status()
    kq = r.json()[0]
    return kq[0] if isinstance(kq, list) else kq


def _dich_mymemory(text):
    r = requests.get("https://api.mymemory.translated.net/get", timeout=15, params={"q": text, "langpair": "en|vi"})
    r.raise_for_status()
    j = r.json()
    if j.get("responseStatus") != 200 or j.get("quotaFinished"):
        raise RuntimeError(j.get("responseDetails") or "hết lượt dịch miễn phí")
    return j["responseData"]["translatedText"]


# Dịch vụ dịch miễn phí, thử lần lượt. Máy chủ GitHub hay bị Google chặn (lỗi 429) nên cần dự phòng.
DICH_VU = [("Google", _dich_google), ("Google 2", _dich_google_2), ("MyMemory", _dich_mymemory)]
_dich_vu_hong = set()   # dịch vụ đã lỗi trong lần chạy này, không thử lại


def dich(text):
    """Dịch sang tiếng Việt. Mọi dịch vụ đều lỗi thì trả None để giữ nguyên bản gốc."""
    for ten, ham in DICH_VU:
        if ten in _dich_vu_hong:
            continue
        try:
            kq = ham(text)
            if kq:
                return kq
        except Exception as e:
            _dich_vu_hong.add(ten)
            log.warning("Dịch vụ dịch %s lỗi (%s), chuyển sang dịch vụ khác", ten, str(e)[:60])
    return None


def dich_tin_nuoc_ngoai(con):
    """Tin giữ lại mà tiêu đề không có dấu tiếng Việt thì dịch tiêu đề và sapo, ghi đè vào kho tin.
    Dịch lỗi thì để dich=0, lần chạy sau thử lại."""
    han = (datetime.now(timezone.utc) - timedelta(hours=LUU_TOI_DA_GIO)).isoformat()
    da_dich = 0
    for id_, tieu_de, tom_tat in con.execute(
            "SELECT id, tieu_de, tom_tat FROM tin WHERE giu=1 AND dich=0 AND thoi_gian>=?", (han,)).fetchall():
        if RE_TIENG_VIET.search(tieu_de):
            con.execute("UPDATE tin SET dich=2 WHERE id=?", (id_,))
            continue
        if len(_dich_vu_hong) == len(DICH_VU):
            log.warning("Tất cả dịch vụ dịch đều lỗi, để lần chạy sau dịch tiếp")
            break
        if da_dich >= DICH_TOI_DA_MOI_LAN:
            break
        sapo = rut_gon_sapo(tom_tat, tieu_de, toi_da=300)  # MyMemory nhận tối đa 500 ký tự
        ban_dich = dich(tieu_de + ("\n" + sapo if sapo else ""))
        if not ban_dich:
            continue
        dong = ban_dich.split("\n", 1)
        con.execute("UPDATE tin SET tieu_de=?, tom_tat=?, dich=1 WHERE id=?",
                    (dong[0].strip(), dong[1].strip() if len(dong) > 1 else "", id_))
        da_dich += 1
    con.commit()
    if da_dich:
        log.info("Đã dịch %d tin nước ngoài", da_dich)


# Bảng giá trên trang HTML: (tên, mã Yahoo Finance, đơn vị). Nguồn Yahoo, giá trễ khoảng 10-15 phút.
BANG_GIA = {
    "hh": ("Hàng hóa", [
        ("Dầu WTI", "CL=F", "USD/thùng"), ("Dầu Brent", "BZ=F", "USD/thùng"),
        ("Khí tự nhiên", "NG=F", "USD/MMBtu"), ("Xăng RBOB", "RB=F", "USD/gallon"),
        ("Dầu sưởi", "HO=F", "USD/gallon"), ("Khí châu Âu (TTF)", "TTF=F", "EUR/MWh"),
        ("Than (API2)", "MTF=F", "USD/tấn"), ("Vàng", "GC=F", "USD/oz"), ("Bạc", "SI=F", "USD/oz"),
        ("Bạch kim", "PL=F", "USD/oz"), ("Đồng", "HG=F", "USD/lb"), ("Nhôm", "ALI=F", "USD/tấn"),
        ("Quặng sắt", "TIO=F", "USD/tấn"), ("Thép HRC (Mỹ)", "HRC=F", "USD/tấn ngắn"),
        ("Đậu tương", "ZS=F", "US cent/giạ"), ("Lúa mì", "ZW=F", "US cent/giạ"), ("Ngô", "ZC=F", "US cent/giạ"),
        ("Gạo thô", "ZR=F", "USD/cwt"), ("Cà phê Arabica", "KC=F", "US cent/lb"), ("Đường", "SB=F", "US cent/lb"),
        ("Bông", "CT=F", "US cent/lb"), ("Gỗ xẻ", "LBR=F", "USD/1000 board feet"),
    ]),
    "cs": ("Chỉ số", [
        ("VN-Index", "^VNINDEX.VN", "điểm"), ("S&P 500", "^GSPC", "điểm"), ("Nasdaq", "^IXIC", "điểm"),
        ("Dow Jones", "^DJI", "điểm"), ("Nikkei 225", "^N225", "điểm"), ("Thượng Hải", "000001.SS", "điểm"),
        ("Hang Seng", "^HSI", "điểm"), ("KOSPI", "^KS11", "điểm"),
    ]),
    "fx": ("Tỷ giá", [
        ("USD/VND", "VND=X", "VND"), ("Chỉ số USD (DXY)", "DX-Y.NYB", "điểm"), ("EUR/USD", "EURUSD=X", "USD"),
        ("USD/JPY", "USDJPY=X", "JPY"), ("USD/CNY", "CNY=X", "CNY"),
    ]),
    "cr": ("Crypto", [("Bitcoin", "BTC-USD", "USD"), ("Ethereum", "ETH-USD", "USD")]),
    "tp": ("Trái phiếu Mỹ", [
        ("Lợi suất 13 tuần", "^IRX", "%"), ("Lợi suất 10 năm", "^TNX", "%"), ("Lợi suất 30 năm", "^TYX", "%"),
    ]),
}


def lay_mot_gia(muc):
    ten, ma, don_vi = muc
    try:
        r = requests.get(f"https://query1.finance.yahoo.com/v8/finance/chart/{ma}", headers=UA, timeout=15,
                         params={"range": "5d", "interval": "1d"})
        r.raise_for_status()
        kq = r.json()["chart"]["result"][0]
        dong = [c for c in kq["indicators"]["quote"][0].get("close", []) if c is not None]  # than API2 hay thiếu
        gia = kq["meta"].get("regularMarketPrice") or dong[-1]
        truoc = dong[-2] if len(dong) >= 2 else kq["meta"].get("chartPreviousClose")
        return {"ten": ten, "ma": ma, "dv": don_vi, "gia": gia, "doi": gia - truoc, "pt": (gia / truoc - 1) * 100,
                "t": kq["meta"].get("regularMarketTime")}
    except Exception as e:
        log.warning("Không lấy được giá %s (%s): %s", ten, ma, str(e)[:60])
        return None


def lay_bang_gia():
    """Giá mới nhất và thay đổi so với phiên trước của các mã trong BANG_GIA."""
    with ThreadPoolExecutor(max_workers=8) as ex:
        bang = {k: (ten, list(ex.map(lay_mot_gia, ds))) for k, (ten, ds) in BANG_GIA.items()}
    return {k: {"ten": ten, "ds": [g for g in ds if g]} for k, (ten, ds) in bang.items()}


# ---- Định giá từ các công ty chứng khoán ----
# CafeF tổng hợp báo cáo "Cập nhật doanh nghiệp - Khuyến nghị" của mọi CTCK (trang công khai).
CAFEF_BAO_CAO = "https://cafef.vn/du-lieu/phan-tich-bao-cao/cap-nhat-doanh-nghiep-khuyen-nghi.chn"
# VCBS công khai danh mục khuyến nghị kèm giá mục tiêu trên trang Trung tâm phân tích.
VCBS_KHUYEN_NGHI = [("CPCTC", "Dài hạn"), ("TPDN", "Ngắn hạn"), ("CPTT", "Cổ tức")]
BAO_CAO_TOI_DA_MOI_LAN = 15
NGAY_BAO_CAO_HTML = 60

KHUYEN_NGHI = ["KÉM KHẢ QUAN", "KHẢ QUAN", "NẮM GIỮ", "TRUNG LẬP", "PHÙ HỢP THỊ TRƯỜNG", "TÍCH LŨY",
               "THEO DÕI", "MUA", "BÁN", "OUTPERFORM", "UNDERPERFORM", "ACCUMULATE", "NEUTRAL", "BUY", "HOLD", "SELL"]
_KN = "|".join(map(re.escape, KHUYEN_NGHI))
RE_KN_SAU_NHAN = re.compile(rf"(?:khuyến nghị|recommendation)\s*(?:đầu tư)?\s*[:\-–]?\s*({_KN})(?![{CHU}])", re.I)
RE_KN_VIET_HOA = re.compile(rf"(?<![{CHU}])({_KN})(?![{CHU}])")  # chữ in hoa trong tiêu đề, vd "HPG/MUA"
RE_GMT = re.compile(r"giá mục tiêu|GMT|giá MT|target price", re.I)
RE_SO = re.compile(r"\d{1,3}(?:[.,]\d{3})+|\d+(?:[.,]\d+)?")


def so_gia(s):
    """'41.100' / '35,900' -> 41100 / 35900; '37,39' (nghìn đồng) -> 37390."""
    if re.fullmatch(r"\d{1,3}(?:[.,]\d{3})+", s):
        return float(re.sub(r"[.,]", "", s))
    v = float(s.replace(",", "."))
    return v * 1000 if v < 1000 else v


def doc_gmt(text):
    """Số đầu tiên sau chữ 'giá mục tiêu' mà hợp lý là giá: bỏ qua năm (2027), % và số dính chữ (Q3)."""
    for m in RE_GMT.finditer(text):
        doan = text[m.end():m.end() + 60]
        for n in RE_SO.finditer(doan):
            s = n.group()
            truoc, sau = doan[n.start() - 1:n.start()], doan[n.end():n.end() + 2].strip()
            if (truoc and truoc.isalpha()) or sau.startswith("%") or re.fullmatch(r"20\d\d", s):
                continue
            v = so_gia(s)
            if 1000 <= v <= 2_000_000:
                return v
    return None


def doc_khuyen_nghi(tieu_de, tom_tat):
    """Khuyến nghị và giá mục tiêu nếu tiêu đề hoặc tóm tắt có ghi; không có thì None."""
    m = RE_KN_SAU_NHAN.search(tom_tat) or RE_KN_SAU_NHAN.search(tieu_de) or RE_KN_VIET_HOA.search(tieu_de)
    kn = m.group(1).upper() if m else None
    return kn, doc_gmt(tieu_de) or doc_gmt(tom_tat)


def doc_chi_tiet_bao_cao(link):
    h = requests.get(link, headers=UA, timeout=20).text
    txt = html.unescape(re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", re.sub(r"<script.*?</script>", " ", h, flags=re.S))))
    lay = lambda mau: (re.search(mau, txt) or [None, ""])[1].strip()
    tieu_de = html.unescape((re.search(r"<title>(.*?)\s*\|", h, re.S) or [None, ""])[1]).strip()
    ngay = lay(r"Ngày phát hành:\s*(\d{2}/\d{2}/\d{4})")
    i = txt.find("Tóm tắt AI")
    tom_tat = txt[i + len("Tóm tắt AI"):txt.find("Khuyến cáo:", i)].strip() if i >= 0 else ""
    ctck = lay(r"Nguồn báo cáo:\s*(.+?)\s*Loại báo cáo:")
    kn, gmt = doc_khuyen_nghi(tieu_de, tom_tat)
    return {
        "link": link, "ma": lay(r"Mã CK:\s*([A-Z0-9]{3,4})\b"), "ctck": ctck,
        "ctck_ngan": ctck.rsplit(" - ", 1)[-1] if " - " in ctck else ctck,
        "tieu_de": tieu_de, "loai": lay(r"Loại báo cáo:\s*(.+?)\s*Ngày phát hành:"),
        "ngay": datetime.strptime(ngay, "%d/%m/%Y").date().isoformat() if ngay else "",
        "tom_tat": tom_tat[:1200], "khuyen_nghi": kn, "gia_muc_tieu": gmt,
    }


def lay_bao_cao_ctck(con):
    """Báo cáo mới trên CafeF: chỉ đọc trang chi tiết của báo cáo chưa có trong kho."""
    trong = con.execute("SELECT COUNT(*) FROM bao_cao").fetchone()[0] == 0
    try:
        h = requests.get(CAFEF_BAO_CAO, headers=UA, timeout=20).text
    except Exception as e:
        log.warning("Không đọc được danh sách báo cáo CafeF: %s", str(e)[:80])
        return
    links = ["https://cafef.vn" + l for l in dict.fromkeys(re.findall(r'href="(/du-lieu/report/[^"?]+\.chn)', h))]
    moi = [l for l in links if not con.execute("SELECT 1 FROM bao_cao WHERE link=?", (l,)).fetchone()]
    bay_gio = datetime.now(timezone.utc).isoformat()
    them = 0
    for link in moi[:BAO_CAO_TOI_DA_MOI_LAN]:
        try:
            bc = doc_chi_tiet_bao_cao(link)
        except Exception as e:
            log.warning("Không đọc được báo cáo %s: %s", link, str(e)[:80])
            continue
        # Lần đầu chỉ ghi nhận báo cáo đang có, không gửi dồn lên Telegram
        con.execute("INSERT OR IGNORE INTO bao_cao (link,ma,ctck,ctck_ngan,tieu_de,loai,ngay,tom_tat,khuyen_nghi,"
                    "gia_muc_tieu,lay_luc,da_gui) VALUES (:link,:ma,:ctck,:ctck_ngan,:tieu_de,:loai,:ngay,:tom_tat,"
                    ":khuyen_nghi,:gia_muc_tieu,:lay_luc,:da_gui)", {**bc, "lay_luc": bay_gio, "da_gui": int(trong)})
        them += 1
    con.commit()
    if them:
        log.info("Thêm %d báo cáo CTCK mới", them)


def lay_khuyen_nghi_vcbs():
    """Danh mục khuyến nghị VCBS, dữ liệu của trang Trung tâm phân tích VCBS (giá tính bằng nghìn đồng).
    Mỗi danh mục có cột riêng (dài hạn: giá mục tiêu; ngắn hạn: vùng mua/cắt lỗ/chốt lời; cổ tức: tỷ suất),
    nên giữ nguyên tên cột VCBS dùng."""
    ket_qua = {}
    for ma_dm, ten in VCBS_KHUYEN_NGHI:
        try:
            r = requests.get("https://www.vcbs.com.vn/api/v1/ttpt-recommendations", headers=UA, timeout=20,
                             params={"category_code": ma_dm, "locale": "vi"})
            r.raise_for_status()
            d = r.json()["data"]
            cot = [(k, re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", v)).strip())
                   for k, v in (d.get("columnsMapping") or {}).items()]
            ket_qua[ma_dm] = {"ten": ten, "ngay": d.get("recommendationDate"), "cot": cot,
                              "ds": d.get("columnsData") or []}
        except Exception as e:
            log.warning("Không lấy được khuyến nghị VCBS %s: %s", ten, str(e)[:80])
    return ket_qua


def soan_bao_cao(rows):
    """Tin nhắn Telegram cho báo cáo CTCK mới."""
    dong = [f"<b>📊 Báo cáo định giá mới từ CTCK — {len(rows)} báo cáo</b>", ""]
    for r in rows:
        phan = [f"<b>[{r['ma']}]</b>" if r["ma"] else "", html.escape(r["ctck_ngan"] or "")]
        if r["khuyen_nghi"]:
            phan.append(f"<b>{html.escape(r['khuyen_nghi'])}</b>")
        if r["gia_muc_tieu"]:
            phan.append(f"GMT {r['gia_muc_tieu']:,.0f}".replace(",", "."))
        dong.append("• " + " · ".join(p for p in phan if p))
        dong.append(f"   <a href=\"{html.escape(r['link'])}\">{html.escape(r['tieu_de'])}</a>")
    return "\n".join(dong)


def xuat_html(con, cfg):
    """Ghi tin_tuc.html: tin đã giữ trong NGAY_HTML ngày gần nhất, nhúng dữ liệu vào tin_tuc_template.html."""
    han = (datetime.now(timezone.utc) - timedelta(days=NGAY_HTML)).isoformat()
    tin = [{
        "t": r["thoi_gian"], "lay": r["lay_luc"], "nhom": r["nhom"], "td": r["tieu_de"], "link": r["link"],
        "sapo": rut_gon_sapo(r["tom_tat"], r["tieu_de"], toi_da=320), "ma": [m for m in r["ma"].split(",") if m],
        "nguon": r["nguon"], "dich": r["dich"] == 1,
    } for r in con.execute("SELECT * FROM tin WHERE giu=1 AND thoi_gian>=? ORDER BY thoi_gian DESC", (han,))]
    du_lieu = {
        "cap_nhat": datetime.now(timezone.utc).isoformat(),
        "uu_tien": [m.strip().upper() for m in cfg.get("cai_dat", "ma_uu_tien", fallback="").split(",") if m.strip()],
        "nhom": TEN_NHOM,
        "tin": tin,
        "gia": lay_bang_gia(),
        "dinh_gia": {
            "vcbs": lay_khuyen_nghi_vcbs(),
            "bao_cao": [{
                "ngay": r["ngay"], "ma": r["ma"], "ctck": r["ctck"], "ctck_ngan": r["ctck_ngan"], "td": r["tieu_de"],
                "link": r["link"], "tom_tat": r["tom_tat"], "kn": r["khuyen_nghi"], "gmt": r["gia_muc_tieu"],
            } for r in con.execute("SELECT * FROM bao_cao WHERE ngay>=? ORDER BY ngay DESC, lay_luc DESC LIMIT 300", (
                (datetime.now(VN_TZ) - timedelta(days=NGAY_BAO_CAO_HTML)).date().isoformat(),))],
        },
    }
    json_str = json.dumps(du_lieu, ensure_ascii=False).replace("</", "<\\/")
    trang = FILE_TEMPLATE.read_text(encoding="utf-8").replace("/*DU_LIEU*/null", json_str)
    tam = FILE_HTML.with_suffix(".tmp")
    tam.write_text(trang, encoding="utf-8")
    tam.replace(FILE_HTML)  # ghi xong mới thay, trình duyệt không đọc phải file dở dang


def soan_tin(rows, uu_tien, nhom_gui):
    """Ghép tin thành các tin nhắn Telegram (HTML, mỗi tin nhắn < 4000 ký tự)."""
    nhom = {}
    for r in rows:
        ma = [m for m in r["ma"].split(",") if m]
        khoa = "uu" if set(ma) & uu_tien else r["nhom"]
        if khoa != "uu" and khoa not in nhom_gui:
            continue
        nhom.setdefault(khoa, []).append(r)
    if not nhom:
        return [], 0
    gio = datetime.now(VN_TZ).strftime("%H:%M %d/%m")
    tong = sum(len(v) for v in nhom.values())
    dong = [f"<b>📰 Tin mới {gio} — {tong} tin</b>"]
    thu_tu = ["uu", "dn", "ck", "cg", "vm", "hh", "qt"]
    for k in thu_tu:
        if k not in nhom:
            continue
        dong.append("")
        dong.append(f"<b>{'⭐ Mã ưu tiên' if k == 'uu' else TEN_NHOM[k]}</b>")
        for r in nhom[k]:
            ma = f"<b>[{r['ma'].replace(',', ' ')}]</b> " if r["ma"] else ""
            nguon = r["nguon"] + (" · dịch máy" if r["dich"] == 1 else "")
            dong.append(f"• {ma}<a href=\"{html.escape(r['link'])}\">{html.escape(r['tieu_de'])}</a>"
                        f" <i>({html.escape(nguon)})</i>")
            sapo = rut_gon_sapo(r["tom_tat"], r["tieu_de"])
            if sapo:
                dong.append(f"   ↳ {html.escape(sapo)}")
    tin_nhan, hien_tai = [], ""
    for d in dong:
        if len(hien_tai) + len(d) + 1 > 3900:
            tin_nhan.append(hien_tai)
            hien_tai = ""
        hien_tai += d + "\n"
    if hien_tai.strip():
        tin_nhan.append(hien_tai)
    return tin_nhan, tong


def gui_telegram(cfg, text):
    token = cfg.get("telegram", "token", fallback="").strip()
    chat_id = cfg.get("telegram", "chat_id", fallback="").strip()
    if not token or not chat_id:
        return False
    r = requests.post(f"https://api.telegram.org/bot{token}/sendMessage", timeout=20, data={
        "chat_id": chat_id, "text": text, "parse_mode": "HTML", "disable_web_page_preview": "true"})
    if not r.ok:
        log.error("Telegram lỗi %s: %s", r.status_code, r.text[:200])
    return r.ok


def chay(cfg):
    tat_ca_ma = doc_ma()
    con = mo_db()
    con.row_factory = sqlite3.Row
    lan_dau = con.execute("SELECT COUNT(*) FROM tin").fetchone()[0] == 0
    tin = thu_thap(tat_ca_ma)
    moi = luu(con, tin)
    log.info("Đọc %d tin, %d tin mới", len(tin), moi)
    con.execute("DELETE FROM tin WHERE thoi_gian < ?",
                ((datetime.now(timezone.utc) - timedelta(days=XOA_SAU_NGAY)).isoformat(),))
    con.commit()
    dich_tin_nuoc_ngoai(con)
    phan_loai_lai(con, tat_ca_ma, doc_ten_goi())
    lay_bao_cao_ctck(con)
    try:
        xuat_html(con, cfg)
    except Exception:
        log.exception("Lỗi xuất HTML (vẫn gửi Telegram bình thường)")

    if lan_dau:
        # Lần chạy đầu: chỉ ghi nhận tin đang có, không gửi dồn hàng trăm tin cũ
        con.execute("UPDATE tin SET da_gui=1")
        con.commit()
        gui_telegram(cfg, f"✅ Hệ thống tin tức đã khởi động, ghi nhận {moi} tin hiện có. "
                          f"Từ lần chạy sau sẽ gửi tin mới.")
        return

    han = (datetime.now(timezone.utc) - timedelta(hours=GUI_TOI_DA_GIO)).isoformat()
    con.execute("UPDATE tin SET da_gui=1 WHERE da_gui=0 AND (giu=0 OR thoi_gian<?)", (han,))
    con.commit()
    if trong_gio_yen_lang(cfg):
        log.info("Đang trong giờ yên lặng, để dành tin")
        return

    rows = con.execute("SELECT * FROM tin WHERE da_gui=0 ORDER BY thoi_gian").fetchall()
    uu_tien = {m.strip().upper() for m in cfg.get("cai_dat", "ma_uu_tien", fallback="").split(",") if m.strip()}
    nhom_gui = {n.strip() for n in cfg.get("cai_dat", "nhom_gui", fallback=",".join(TEN_NHOM)).split(",")}
    tin_nhan, tong = soan_tin(rows, uu_tien, nhom_gui)
    for t in tin_nhan:
        if not gui_telegram(cfg, t):
            log.warning("Chưa gửi được Telegram (chưa cấu hình hoặc lỗi mạng), sẽ thử lại lần sau")
            return
    con.execute("UPDATE tin SET da_gui=1 WHERE da_gui=0")
    con.commit()
    log.info("Đã gửi %d tin trong %d tin nhắn", tong, len(tin_nhan))

    bao_cao = con.execute("SELECT * FROM bao_cao WHERE da_gui=0 ORDER BY ngay, lay_luc").fetchall()
    if bao_cao and cfg.get("cai_dat", "gui_bao_cao_ctck", fallback="yes").strip().lower() != "no":
        for i in range(0, len(bao_cao), 12):   # 12 báo cáo mỗi tin nhắn, dưới giới hạn 4096 ký tự
            nhom = bao_cao[i:i + 12]
            if not gui_telegram(cfg, soan_bao_cao(nhom)):
                return
            con.executemany("UPDATE bao_cao SET da_gui=1 WHERE link=?", [(r["link"],) for r in nhom])
            con.commit()
        log.info("Đã gửi %d báo cáo CTCK", len(bao_cao))


def chay_thu():
    tin = thu_thap(doc_ma())
    giu = [t for t in tin if t["giu"]]
    print(f"Đọc {len(tin)} tin, giữ {len(giu)} tin\n")
    for k, ten in TEN_NHOM.items():
        nhom = [t for t in giu if t["nhom"] == k]
        print(f"== {ten}: {len(nhom)} tin")
        for t in nhom[:5]:
            print(f"   [{t['ma']}] {t['tieu_de'][:90]} ({t['nguon']})")


def setup(cfg):
    token = cfg.get("telegram", "token", fallback="").strip()
    if not token:
        print("Chưa có token. Tạo file bi_mat.ini với 2 dòng:\n[telegram]\ntoken = <token của bot>\nrồi chạy lại.")
        return
    r = requests.get(f"https://api.telegram.org/bot{token}/getUpdates", timeout=20).json()
    if not r.get("ok"):
        print("Token không đúng:", r.get("description"))
        return
    chats = [u["message"]["chat"] for u in r["result"] if "message" in u]
    if not chats:
        print("Bot chưa nhận được tin nhắn nào. Mở Telegram, tìm bot của bạn, bấm Start "
              "hoặc gửi một chữ bất kỳ, rồi chạy lại lệnh này.")
        return
    chat = chats[-1]
    cfg.set("telegram", "chat_id", str(chat["id"]))
    FILE_BI_MAT.write_text(
        "# File bí mật: KHÔNG chia sẻ, KHÔNG đưa lên GitHub (đã có trong .gitignore)\n"
        f"[telegram]\ntoken = {token}\nchat_id = {chat['id']}\n", encoding="utf-8")
    ten = chat.get("first_name") or chat.get("title") or ""
    print(f"Đã lưu chat_id {chat['id']} ({ten}).")
    if gui_telegram(cfg, "✅ Kết nối thành công! Bot tin tức sẽ gửi tin vào đây."):
        print("Đã gửi tin nhắn thử, hãy kiểm tra Telegram.")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--thu", action="store_true")
    ap.add_argument("--setup", action="store_true")
    a = ap.parse_args()
    if sys.stdout:
        sys.stdout.reconfigure(encoding="utf-8")
    cfg = doc_config()
    if a.setup:
        setup(cfg)
    elif a.thu:
        chay_thu()
    else:
        cai_log()
        try:
            chay(cfg)
        except Exception:
            log.exception("Lỗi khi chạy")


if __name__ == "__main__":
    main()
