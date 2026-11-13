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
from datetime import date, datetime, timedelta, timezone
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
FILE_MA_HNX = THU_MUC / "ma_hnx.csv"   # mã sàn HNX: chỉ để gắn mã cho tin, bảng KQKD vẫn chỉ quét HOSE
FILE_TEN = THU_MUC / "ten_goi_khac.csv"
FILE_TU_KHOA_LOAI = THU_MUC / "tu_khoa_loai.txt"
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
    ("CafeF", "https://cafef.vn/thi-truong-chung-khoan.rss", "ck", True),
    ("CafeF", "https://cafef.vn/doanh-nghiep.rss", "dn", True),
    ("CafeF", "https://cafef.vn/vi-mo-dau-tu.rss", "vm", True),
    ("CafeF", "https://cafef.vn/tai-chinh-ngan-hang.rss", "vm", False),
    ("CafeF", "https://cafef.vn/thi-truong.rss", "hh", True),
    ("CafeF", "https://cafef.vn/tai-chinh-quoc-te.rss", "qt", True),
    ("Vietstock", "https://vietstock.vn/830/chung-khoan/co-phieu.rss", "ck", True),
    ("Vietstock", "https://vietstock.vn/737/doanh-nghiep/hoat-dong-kinh-doanh.rss", "dn", True),
    ("Vietstock", "https://vietstock.vn/738/doanh-nghiep/co-tuc.rss", "dn", True),
    ("Vietstock", "https://vietstock.vn/739/chung-khoan/giao-dich-noi-bo.rss", "dn", True),
    ("Vietstock", "https://vietstock.vn/741/chung-khoan/niem-yet.rss", "dn", True),
    ("Vietstock", "https://vietstock.vn/764/doanh-nghiep/tang-von-m-a.rss", "dn", True),
    ("Vietstock", "https://vietstock.vn/145/chung-khoan/y-kien-chuyen-gia.rss", "cg", False),
    ("Vietstock", "https://vietstock.vn/1636/nhan-dinh-phan-tich/nhan-dinh-thi-truong.rss", "cg", False),
    ("Vietstock", "https://vietstock.vn/582/nhan-dinh-phan-tich/phan-tich-co-ban.rss", "cg", False),
    ("Vietstock", "https://vietstock.vn/143/chung-khoan/chinh-sach.rss", "vm", False),
    ("Vietstock", "https://vietstock.vn/761/kinh-te/vi-mo.rss", "vm", False),
    ("Vietstock", "https://vietstock.vn/757/tai-chinh/ngan-hang.rss", "vm", False),
    ("Vietstock", "https://vietstock.vn/2/hang-hoa.rss", "hh", False),
    ("Vietstock", "https://vietstock.vn/773/the-gioi/chung-khoan-the-gioi.rss", "qt", False),
    ("Vietstock", "https://vietstock.vn/772/the-gioi/tai-chinh-quoc-te.rss", "qt", False),
    ("TNCK", "https://tinnhanhchungkhoan.vn/rss/chung-khoan-2.rss", "ck", True),
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
    "bds": "🏘 Bất động sản",
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
# Dự án năng lượng, hợp đồng lớn: giữ ở cả chuyên mục Vĩ mô và Doanh nghiệp
# (góp ý 13/11: tin PTSC ký hợp đồng Nhiệt điện Long Phú 1 ở mục Doanh nghiệp CafeF bị lọc mất)
TU_KHOA_DU_AN = [
    "nhiệt điện", "điện khí", "điện gió", "điện mặt trời", "nhà máy điện", "điện hạt nhân", "giá phát điện", "lng",
    "gói thầu", "hợp đồng bot", "quyền thu phí", "siêu cảng",
]
TU_KHOA_VN += TU_KHOA_DU_AN
# Chuyên mục Doanh nghiệp: chỉ giữ tin không gắn mã khi nói về tài chính doanh nghiệp, thị trường vốn
# (từ vĩ mô chung như "xuất khẩu" làm lọt tin không liên quan, vd giải thưởng khoa học)
TU_KHOA_DN = [
    "cổ phiếu", "cổ tức", "chứng khoán", "trái phiếu", "lợi nhuận", "doanh thu", "lãi ròng", "kqkd",
    "kết quả kinh doanh", "niêm yết", "thoái vốn", "sáp nhập", "m&a", "ipo", "cổ đông", "đhđcđ", "tăng vốn",
    "phát hành", "giá điện", "lãi suất", "tỷ giá", "khối ngoại",
]
TU_KHOA_DN += TU_KHOA_DU_AN

# Chuyên mục Chứng khoán: chỉ giữ tin không gắn mã khi nói về thị trường vốn
# (lọc tin quy hoạch đô thị, vụ hack tiền điện tử, siêu xe... mà báo đăng ở mục chứng khoán)
TU_KHOA_CK = [
    "chứng khoán", "cổ phiếu", "vn-index", "vnindex", "vn30", "khối ngoại", "thanh khoản", "dòng tiền", "phiên",
    "cổ tức", "niêm yết", "trái phiếu", "etf", "tự doanh", "margin", "nâng hạng", "lãi suất", "tỷ giá",
    "lợi nhuận", "doanh thu", "kqkd", "kết quả kinh doanh", "cổ đông", "thao túng", "ubcknn", "phái sinh",
]

# Phân loại theo nội dung tiêu đề (chuyên mục của báo chỉ là gợi ý ban đầu)
RE_HANG_HOA = re.compile(
    r"giá (vàng|bạc|dầu|xăng|thép|tôn|cà phê|cao su|gạo|lúa|hồ tiêu|tiêu|heo|lợn|phân bón|than|quặng|đường|điều|"
    r"sầu riêng|nông sản)|vàng (miếng|nhẫn|sjc)|^vàng (thế giới |trong nước )?(rơi|lao|tăng|giảm|bật|lập)", re.I)
# Tin ngành hàng nông sản, nguyên liệu (không chỉ tin giá) cũng là Hàng hóa (góp ý 04/11: "Mở đường đưa trà Việt
# thoát 'bẫy' xuất thô"), trừ khi tiêu đề nói về doanh nghiệp niêm yết cụ thể
RE_NGANH_HANG = re.compile(
    r"\b(trà|chè|cà phê|gạo|lúa gạo|hồ tiêu|hạt tiêu|hạt điều|cao su|sầu riêng|nông sản|thủy sản|cá tra|tôm|"
    r"thép|phân bón|dầu thô|xăng dầu|quặng|đường mía|ca cao)\b", re.I)
# Tin nước ngoài về vàng, dầu, kim loại... là Hàng hóa, không phải Quốc tế (góp ý 04/11: tin Kitco về vàng, bạc)
RE_HANG_HOA_EN = re.compile(
    r"\b(gold|silver|oil|crude|brent|wti|copper|platinum|palladium|iron ore|steel|aluminium|aluminum|"
    r"commodit(y|ies)|opec\+?|natural gas|lng|wheat|corn|soybeans?|coffee|sugar|cocoa|bullion|precious metals?)\b", re.I)
# Tin báo ngoại đã dịch (tiêu đề lưu bằng tiếng Việt): nhận Hàng hóa theo bản dịch
RE_HANG_HOA_DICH = re.compile(
    r"\b(vàng|(?<!kho )bạc|giá dầu|dầu thô|dầu mỏ|dầu brent|kim loại quý|bạch kim|quặng sắt|khí đốt|lng|lúa mì|"
    r"đậu tương|ca cao|hàng hóa|opec\+?)\b", re.I)
# Tin trái phiếu, cổ phiếu, Fed... chỉ nhắc giá dầu/vàng ("Treasuries fall amid oil volatility") vẫn là Quốc tế:
# khi tiêu đề có các từ này, hàng hóa phải đứng ở đầu tiêu đề mới tính là tin Hàng hóa
RE_TAI_CHINH_NGOAI = re.compile(
    r"\b(treasur(y|ies)|yields?|bonds?|stocks?|equit(y|ies)|s&p|nasdaq|dow|wall street|fed|dollar|currenc(y|ies)|"
    r"forex|rupee|yen|euro|yuan|sensex|nikkei|earnings)\b|"
    r"kho bạc|trái phiếu|lợi suất|cổ phiếu|chứng khoán|phố wall|đô la|đồng usd|tiền tệ|tỷ giá|rupee|đồng yên|"
    r"nhân dân tệ|sensex|nikkei|thu nhập|lợi nhuận", re.I)


def la_hang_hoa_ngoai(tieu_de, da_dich):
    m = RE_HANG_HOA_EN.search(tieu_de) or (da_dich and RE_HANG_HOA_DICH.search(tieu_de))
    return bool(m) and (m.start() < 12 or not RE_TAI_CHINH_NGOAI.search(tieu_de))


# Bài bảng giá, lãi suất hằng ngày: nhắc tên nhiều ngân hàng, tiệm vàng nhưng không phải tin doanh nghiệp
RE_TONG_HOP = re.compile(r"^(giá|lãi suất|tỷ giá|biểu lãi suất)\b.*(ngày|hôm nay|sáng|chiều|\d{1,2}/\d{1,2})", re.I)
RE_NGU_CANH_MA = r"(?i:\(|mã\s+|cổ phiếu\s+|cp\s+|hose:\s*|hsx:\s*){m}(?![{chu}])"
# Sự kiện riêng của một doanh nghiệp (cổ tức, nhân sự, KQKD...): tin ở chuyên mục Chứng khoán vẫn là tin Doanh nghiệp
RE_SU_KIEN_DN = re.compile(
    r"cổ tức|nhân sự|tổng giám đốc|chủ tịch|hđqt|hội đồng quản trị|đhđcđ|đại hội cổ đông|phát hành|tăng vốn|"
    r"kqkd|kết quả kinh doanh|lợi nhuận|doanh thu|lãi (ròng|trước thuế|sau thuế)|thua lỗ|báo lỗ|mua lại cổ phiếu|"
    r"thoái vốn|sáp nhập|m&a|người nội bộ|người có liên quan|đăng ký (mua|bán)|kế hoạch kinh doanh|"
    r"báo cáo tài chính|bctc|khởi tố|bắt tạm giam|công bố thông tin|chốt quyền|doanh nghiệp", re.I)
# Tiêu đề nói về cả thị trường thì vẫn là tin Thị trường chứng khoán.
# Theo góp ý: lịch công bố thông tin, lịch chốt cổ tức, "nhiều doanh nghiệp..." là tin Doanh nghiệp, không đưa vào đây.
RE_THI_TRUONG = re.compile(
    r"vn-?index|vn30|hnx-?index|upcom|thị trường|khối ngoại|thanh khoản|phiên|dòng tiền|nhóm cổ phiếu|"
    r"nhóm ngành|chỉ số|margin|công ty chứng khoán|ctck|ngành|ubcknn|ủy ban chứng khoán|chứng khoán", re.I)
# Tiêu đề chỉ nói về một sự kiện riêng của doanh nghiệp (nhân sự, cổ tức...), không nói về cả thị trường:
# tin Doanh nghiệp dù tên công ty có chữ "Chứng khoán" (góp ý 04/11: "Chứng khoán Thành Công bổ nhiệm Phó TGĐ")
RE_SU_KIEN_RIENG = re.compile(
    r"bổ nhiệm|miễn nhiệm|từ nhiệm|tổng giám đốc|chủ tịch|hđqt|hội đồng quản trị|cổ tức|đhđcđ|đại hội cổ đông|"
    r"tăng vốn|người nội bộ|chốt quyền", re.I)
RE_THI_TRUONG_CHUNG = re.compile(
    r"vn-?index|vn30|hnx-?index|upcom|thị trường|khối ngoại|thanh khoản|phiên|dòng tiền|nhóm cổ phiếu|"
    r"nhóm ngành|chỉ số|margin|ngành|ubcknn|ủy ban chứng khoán|nhiều (công ty|doanh nghiệp)", re.I)
# Tin Vĩ mô nói về sự kiện riêng của doanh nghiệp (kể cả mã sàn HNX/UPCoM không có trong ma_hose.csv) là Doanh nghiệp
# (góp ý 10/11: "Giáo sư giàu nhất Việt Nam đối đầu với các quỹ ngoại thâu tóm ngược doanh nghiệp" - Vicostone)
RE_DN_TRONG_VI_MO = re.compile(
    r"cổ tức|đhđcđ|đại hội cổ đông|hđqt|hội đồng quản trị|chốt (danh sách|quyền)|thâu tóm|người kiểm soát|"
    r"thoái vốn|tổng giám đốc|gom .{0,20}cổ phiếu|cổ phiếu từng|cổ đông (ngoại|lớn)|quỹ ngoại", re.I)
RE_VI_MO_CHUNG = re.compile(
    r"ngân hàng nhà nước|nhnn|lãi suất|tỷ giá|gdp|cpi|lạm phát|ngân sách|đầu tư công|chính phủ|thủ tướng|"
    r"bộ tài chính|quốc hội|nghị định|chủ tịch nước|tổng bí thư", re.I)
# Tin nhân sự, lương thưởng, văn hóa doanh nghiệp không gắn mã: không liên quan đầu tư, bỏ
# (góp ý 11/11: "'Vua tiêu' Phan Minh Thông: Phúc Sinh sẵn sàng trả một nhân sự 21 tháng lương/năm" - lọt vì có chữ "lãi suất")
RE_NHAN_SU_PHUC_LOI = re.compile(
    r"tháng lương|thưởng tết|lương thưởng|văn hoá doanh nghiệp|văn hóa doanh nghiệp|phúc lợi|tuyển dụng|"
    r"thu hút nhân tài|giữ chân nhân", re.I)
# Bài giới thiệu doanh nghiệp, startup không niêm yết ("Một DN Việt Nam sản xuất 'mắt thần' cho máy bay không người lái")
# không liên quan đầu tư: bỏ khi không gắn mã và tiêu đề không nói về cổ tức, cổ phiếu, lợi nhuận... (góp ý 12/11)
RE_GIOI_THIEU_DN = re.compile(
    r"^(một|1) (dn|doanh nghiệp|công ty|startup|start-up|tập đoàn|nhà máy|thương hiệu|hãng)\b|\bstartup\b|start-up", re.I)
RE_DN_CO_GIA_TRI_DAU_TU = re.compile(
    r"cổ tức|cổ phiếu|niêm yết|lãi ròng|báo lãi|báo lỗ|lợi nhuận|thua lỗ|phá sản|vỡ nợ|trái phiếu|thoái vốn|sáp nhập|"
    r"m&a|ipo", re.I)
# Tin giải trí, sự kiện tài trợ, marketing (concert, triển lãm, fan...) không liên quan đầu tư, kể cả khi gắn mã ngân hàng
# tài trợ (góp ý 12/11: "Dư âm hai đêm concert... triển lãm kỷ niệm 20 năm BigBang" - VPBank)
RE_GIAI_TRI = re.compile(
    r"concert|liveshow|live show|triển lãm|\bfan\b|người hâm mộ|ca sĩ|idol|k-?pop|showbiz|hoa hậu|nghệ sĩ|"
    r"lễ hội|đại nhạc hội|âm nhạc|khán giả|giải chạy|marathon|giải golf|bóng đá|cầu thủ|phim|diễn viên|rapper", re.I)
# Vụ án hình sự của cá nhân (lừa đảo, chủ hụi, cựu giám đốc chi nhánh bị xử vắng mặt...) không liên quan
# tài chính - doanh nghiệp: bỏ (góp ý 04/11, 10/11).
# Vẫn giữ khi tiêu đề nhắc doanh nghiệp, ngân hàng, chứng khoán... (vd "Ông Nguyễn Hữu Chỉnh bị bắt, doanh nghiệp báo lãi")
RE_HINH_SU = re.compile(
    r"khởi tố|bắt tạm giam|tạm giam|bị bắt|lừa đảo|chiếm đoạt|truy nã|truy tố|cáo trạng|xét xử|tuyên án|hầu tòa|"
    r"án tù|tử hình|chủ hụi|vỡ hụi|hốt hụi|xử vắng mặt|bị xử|bị cáo|phiên tòa|phiên xử|tòa tuyên|kêu oan|"
    r"đơn đề nghị làm rõ", re.I)
TU_KHOA_TAI_CHINH_TD = TU_KHOA_VN + ["doanh nghiệp", "ngân hàng", "công ty", "tập đoàn", "thao túng", "ubcknn"]
# Tin thị trường nhà đất (góp ý 04/11: "Đất nền chật vật tìm đầu ra" -> mục Bất động sản riêng).
# Tiêu đề chung chung ("Mức giá phù hợp quyết định sức mua nhà") thì nhận theo sapo: từ 2 cụm nhà đất khác nhau trở lên.
# Tin về doanh nghiệp (1-2 mã trong tiêu đề, KQKD, cổ phiếu, "đại gia bất động sản", "TTC Land"...) vẫn là tin Doanh nghiệp.
RE_BDS = re.compile(
    r"bất động sản|bbđsb|đất nền|căn hộ|chung cư|nhà ở xã hội|nhà ở thương mại|giá nhà|giá đất|giá thuê nhà|"
    r"phân lô|bán nền|condotel|biệt thự|nhà phố|shophouse|nhà đất|horea|sốt đất|khu đô thị|dự án nhà ở|"
    r"đấu giá (quyền sử dụng )?đất|khu đất|tiền sử dụng đất|khu dân cư|quỹ đất|giao đất|cho thuê đất|"
    r"mua nhà|thị trường nhà|nhà ở|phòng trọ|nhà trọ|cho thuê nhà|cho thuê phòng|nhà cho thuê|căn hộ dịch vụ|"
    r"homestay|ký túc xá|"
    r"[\d.,]+\s?(m2|m²|ha) đất", re.I)
# Tin nói về cả thị trường cổ phiếu, từ bất kỳ nguồn nào ("VN-Index bật tăng, nhóm bất động sản khởi sắc" - Bnews)
RE_THI_TRUONG_NHA_DAT = re.compile(r"thị trường (bất động sản|bđs|nhà ở|nhà đất|nhà|căn hộ|đất nền)", re.I)
RE_CHI_SO = re.compile(r"vn-?index|vn30|hnx-?index|khối ngoại|nhóm cổ phiếu", re.I)
RE_BDS_DOANH_NGHIEP = re.compile(r"cổ phiếu|đại gia|\bland\b|tập đoàn|công ty|niêm yết|khoản nợ", re.I)
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


_ma_hnx = None


def doc_ma_hnx():
    """{mã: được nhận khi đứng một mình không}. Mã HNX trùng từ thông dụng (CEO, API, NET, MST...) chỉ nhận khi có
    ngữ cảnh "mã X", "cổ phiếu X", "(X)"; mã quen thuộc (PVS, SHS, IDC...) nhận như mã HOSE."""
    global _ma_hnx
    if _ma_hnx is None:
        _ma_hnx = {}
        if FILE_MA_HNX.exists():
            with open(FILE_MA_HNX, encoding="utf-8") as f:
                _ma_hnx = {r["ma"].strip().upper(): r["tu_do"].strip() == "1" for r in csv.DictReader(f)}
    return _ma_hnx


def doc_ma_gan():
    """Mã dùng để gắn vào tin, nhận lệnh theo dõi của bot: HOSE + HNX (góp ý 13/11: tin PTSC/PVS bị lọc mất)."""
    return doc_ma() | set(doc_ma_hnx())


def doc_ten_goi():
    """Tên công ty hay xuất hiện trong bài báo -> mã, đọc từ ten_goi_khac.csv (bạn tự thêm được)."""
    if not FILE_TEN.exists():
        return []
    with open(FILE_TEN, encoding="utf-8") as f:
        # dòng bắt đầu bằng "re:" là biểu thức chính quy (vd "MB" là MBB nhưng "Chứng khoán MB" là MBS)
        return [(re.compile(r["ten"].strip()[3:] if r["ten"].strip().startswith("re:")
                            else rf"(?<![{CHU}]){re.escape(r['ten'].strip())}(?![{CHU}])", re.I),
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
        if (m in MA_DE_NHAM or doc_ma_hnx().get(m) is False) and not co_ngu_canh_ma(m, text):
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
        nhom = "hh" if la_hang_hoa_ngoai(tieu_de, False) else nhom_nguon
        return nhom, [], (nhom == "hh" or bool(TU_KHOA_EN.search(noi_dung))) if loc else True
    ma = tim_ma(noi_dung, tat_ca_ma, ten_goi) if nhom_nguon != "qt" else []
    tong_hop = bool(RE_TONG_HOP.search(tieu_de))
    nhom = nhom_nguon
    ma_td = [m for m in ma if m in tim_ma(tieu_de, tat_ca_ma, ten_goi)] if nhom_nguon != "qt" else []
    # "thị trường bất động sản/nhà ở" không phải tin thị trường chứng khoán (góp ý 12/11)
    td_ck = RE_THI_TRUONG_NHA_DAT.sub("", tieu_de)
    tin_thi_truong = bool(RE_CHI_SO.search(tieu_de)) or (
        nhom_nguon == "ck" and (RE_THI_TRUONG_CHUNG.search(td_ck) or "cổ phiếu" in td_ck.lower()))
    if nhom_nguon != "qt" and RE_HANG_HOA.search(tieu_de):
        nhom = "hh"
    elif nhom_nguon in ("vm", "dn") and RE_CHI_SO.search(tieu_de) and not 1 <= len(ma_td) <= 2:
        nhom = "ck"   # tin chỉ số, khối ngoại từ nguồn kinh tế chung
    elif nhom_nguon != "qt" and not ma_td and not tin_thi_truong and RE_NGANH_HANG.search(tieu_de):
        nhom = "hh"
    elif (nhom_nguon != "qt" and not tin_thi_truong and not 1 <= len(ma_td) <= 2
          and (RE_BDS.search(tieu_de) or (not ma and len({m.group(0).lower() for m in RE_BDS.finditer(tom_tat)}) >= 2))
          # "doanh thu" của hộ cho thuê phòng trọ không phải dấu hiệu tin doanh nghiệp (góp ý 13/11)
          and not RE_SU_KIEN_DN.search(re.sub(r"doanh thu", "", tieu_de, flags=re.I))
          and not RE_BDS_DOANH_NGHIEP.search(tieu_de)):
        nhom = "bds"
    elif nhom_nguon == "vm" and not tong_hop:
        if 1 <= len(ma_td) <= 2 or (RE_DN_TRONG_VI_MO.search(tieu_de) and not RE_VI_MO_CHUNG.search(tieu_de)):
            nhom = "dn"
    elif nhom_nguon == "dn" and not ma and not (
            RE_DN_TRONG_VI_MO.search(tieu_de) and not RE_VI_MO_CHUNG.search(tieu_de)):
        nhom = "vm"   # chuyên mục Doanh nghiệp nhưng không gắn được công ty niêm yết nào: tin kinh tế chung
    elif nhom_nguon == "ck" and (
            (not RE_THI_TRUONG.search(tieu_de) and (RE_SU_KIEN_DN.search(noi_dung) or 1 <= len(ma) <= 2))
            or (RE_SU_KIEN_RIENG.search(tieu_de) and not RE_THI_TRUONG_CHUNG.search(tieu_de))):
        # tin về một doanh nghiệp cụ thể: "Doanh nghiệp có nữ Tổng giám đốc... phát thông báo quan trọng",
        # "Taseco Land (TAL) khánh thành...", "Tỷ phú Phạm Nhật Vượng huy động 20.000 người..." (VIC qua VinFast)
        nhom = "dn"
    if tong_hop or nhom == "hh":
        ma = [m for m in ma if co_ngu_canh_ma(m, noi_dung)]
    tu_khoa = {"dn": TU_KHOA_DN, "ck": TU_KHOA_CK}.get(nhom_nguon, TU_KHOA_VN)
    giu = (bool(ma) or nhom in ("dn", "hh", "bds") or any(k in noi_dung.lower() for k in tu_khoa)) if loc else True
    if RE_GIAI_TRI.search(tieu_de) and not RE_DN_CO_GIA_TRI_DAU_TU.search(tieu_de):
        giu = False   # tin giải trí, sự kiện tài trợ
    if RE_GIOI_THIEU_DN.search(tieu_de) and not ma and not RE_DN_CO_GIA_TRI_DAU_TU.search(tieu_de):
        giu = False   # bài giới thiệu doanh nghiệp không niêm yết
    if RE_NHAN_SU_PHUC_LOI.search(tieu_de) and not ma:
        giu = False   # tin nhân sự, lương thưởng của doanh nghiệp không niêm yết
    if (RE_HINH_SU.search(tieu_de) and not ma
            and not any(k in tieu_de.lower() for k in TU_KHOA_TAI_CHINH_TD)):
        giu = False   # vụ án của cá nhân, không liên quan tài chính
    if any(k in tieu_de.lower() for k in doc_tu_khoa_loai()):
        giu = False   # người dùng đã góp ý là tin không liên quan
    return nhom, ma, giu


_tu_khoa_loai = None


def doc_tu_khoa_loai():
    """Cụm từ trong tu_khoa_loai.txt (mỗi dòng một cụm, dòng # là ghi chú): tiêu đề chứa cụm từ này thì bỏ tin."""
    global _tu_khoa_loai
    if _tu_khoa_loai is None:
        _tu_khoa_loai = [d.strip().lower() for d in FILE_TU_KHOA_LOAI.read_text(encoding="utf-8").splitlines()
                         if d.strip() and not d.startswith("#")] if FILE_TU_KHOA_LOAI.exists() else []
    return _tu_khoa_loai


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
    con.execute("""CREATE TABLE IF NOT EXISTS cong_bo (
        link TEXT PRIMARY KEY, ma TEXT, tieu_de TEXT, thoi_gian TEXT, lay_luc TEXT, da_gui INTEGER DEFAULT 0)""")
    # giá trong nước theo ngày, để tính % thay đổi so với ngày trước
    con.execute("CREATE TABLE IF NOT EXISTS gia_tn (ngay TEXT, ma TEXT, ban REAL, PRIMARY KEY (ngay, ma))")
    # chuỗi số liệu theo ngày cho biểu đồ (lãi suất tiết kiệm, TPCP 10 năm) khi nguồn chỉ có số hiện tại
    con.execute("CREATE TABLE IF NOT EXISTS chuoi (ma TEXT, ngay TEXT, gia REAL, PRIMARY KEY (ma, ngay))")
    # KQKD quý gần nhất của từng mã: doanh thu, LNST công ty mẹ, cùng kỳ năm trước (nghìn đồng)
    con.execute("""CREATE TABLE IF NOT EXISTS kqkd (
        ma TEXT PRIMARY KEY, quy TEXT, dt REAL, dt_ck REAL, ln REAL, ln_ck REAL, phat_hien TEXT, cap_nhat TEXT)""")
    # người xem đăng ký nhận thông báo qua bot; moc = thời điểm đã gửi thông báo tới
    con.execute("CREATE TABLE IF NOT EXISTS nguoi_dung (chat_id TEXT PRIMARY KEY, ten TEXT, dang_ky TEXT, moc TEXT)")
    con.execute("CREATE TABLE IF NOT EXISTS theo_doi (chat_id TEXT, ma TEXT, PRIMARY KEY (chat_id, ma))")
    con.execute("CREATE TABLE IF NOT EXISTS cau_hinh (khoa TEXT PRIMARY KEY, gia_tri TEXT)")
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
    Tin đã bỏ cũng được xét lại: luật mới giữ thì hiện lại trên web (tin bỏ đã đánh dấu da_gui=1 nên không gửi lại Telegram)."""
    han = (datetime.now(timezone.utc) - timedelta(days=NGAY_HTML)).isoformat()
    doi = 0
    for r in con.execute("SELECT * FROM tin WHERE thoi_gian>=?", (han,)).fetchall():
        nhom_goc = r["nhom_nguon"] or r["nhom"]
        if r["tieng_viet"] is None:
            if r["nhom"] == "qt":   # tin cũ chưa ghi nguồn: không biết là báo Việt hay báo ngoại
                continue
            # tin cũ: chuyên mục Chứng khoán, Doanh nghiệp nay có lọc; các nguồn khác giữ như lúc lấy
            loc, tieng_viet = nhom_goc in ("ck", "dn"), True
        else:
            # tin lấy trước khi bật lọc cho chuyên mục Chứng khoán, Doanh nghiệp ghi loc=0
            loc, tieng_viet = bool(r["loc"]) or nhom_goc in ("ck", "dn"), bool(r["tieng_viet"])
            if not tieng_viet:   # tin báo ngoại: đã dịch nên không áp lại bộ lọc từ khóa tiếng Anh, chỉ nhận Hàng hóa
                if not r["giu"]:
                    continue
                nhom = "hh" if la_hang_hoa_ngoai(r["tieu_de"], r["dich"] == 1) else nhom_goc
                if nhom != r["nhom"]:
                    con.execute("UPDATE tin SET nhom=?, nhom_nguon=? WHERE id=?", (nhom, nhom_goc, r["id"]))
                    doi += 1
                continue
        nhom, ma, giu = phan_loai(r["tieu_de"], r["tom_tat"] or "", nhom_goc, loc, tieng_viet, tat_ca_ma, ten_goi)
        ma = ",".join(ma)
        if (nhom, ma, int(giu)) != (r["nhom"], r["ma"], r["giu"]):
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


# ---- Công bố thông tin của doanh nghiệp niêm yết (RSS chính thức của HOSE) ----
HOSE_CONG_BO_RSS = "https://api.hsx.vn/n/api/v1/News/NewsByCateFeed/21"   # 10 công bố mới nhất
NGAY_CONG_BO_HTML = 7


def lay_cong_bo(con):
    trong = con.execute("SELECT COUNT(*) FROM cong_bo").fetchone()[0] == 0
    try:
        r = requests.get(HOSE_CONG_BO_RSS, headers=UA, timeout=20)
        r.raise_for_status()
        entries = feedparser.parse(r.content).entries
    except Exception as e:
        log.warning("Không đọc được công bố thông tin HOSE: %s", str(e)[:80])
        return
    bay_gio = datetime.now(timezone.utc).isoformat()
    them = 0
    for e in entries:
        tieu_de = lam_sach(e.get("title"))
        # link trong RSS (api.hsx.vn) mở ra trang trắng; trang tin thật nằm ở www.hsx.vn/vi/tin-tuc/...
        link = e.get("link", "").replace("https://api.hsx.vn/tin-tuc/", "https://www.hsx.vn/vi/tin-tuc/")
        thoi_gian = doc_ngay(e)
        if not tieu_de or not link or thoi_gian is None:
            continue
        ma, _, noi_dung = tieu_de.partition(":")
        cur = con.execute("INSERT OR IGNORE INTO cong_bo VALUES (?,?,?,?,?,?)",
                          (link, ma.strip() if noi_dung else "", (noi_dung or tieu_de).strip(),
                           thoi_gian.isoformat(), bay_gio, int(trong)))
        them += cur.rowcount
    con.commit()
    if them:
        log.info("Thêm %d công bố thông tin HOSE", them)


def soan_cong_bo(rows, uu_tien):
    dong = [f"<b>📢 Công bố thông tin HOSE — {len(rows)} tin</b>", ""]
    for r in sorted(rows, key=lambda r: (r["ma"] not in uu_tien, r["thoi_gian"])):
        gio = datetime.fromisoformat(r["thoi_gian"]).astimezone(VN_TZ).strftime("%H:%M %d/%m")
        sao = "⭐ " if r["ma"] in uu_tien else ""
        dong.append(f"• {sao}<b>[{html.escape(r['ma'])}]</b> {gio} "
                    f"<a href=\"{html.escape(r['link'])}\">{html.escape(r['tieu_de'])}</a>")
    return "\n".join(dong)


# ---- Giá trong nước: vàng SJC, tỷ giá Vietcombank ----
SJC_LOAI = {1: "Vàng SJC miếng", 49: "Vàng nhẫn SJC 99,99"}
VCB_NGOAI_TE = ["USD", "EUR", "CNY", "JPY", "KRW", "SGD", "GBP"]


def lay_gia_trong_nuoc(con):
    """Giá mua/bán vàng SJC (triệu đồng/lượng) và tỷ giá Vietcombank (đồng), % so với ngày trước."""
    ds = []
    try:
        r = requests.post("https://sjc.com.vn/GoldPrice/Services/PriceService.ashx", headers=UA, timeout=20,
                          data={"method": "GetCurrentGoldPricesByBranch", "BranchId": "1"})
        r.raise_for_status()
        for x in r.json()["data"]:
            if x["Id"] in SJC_LOAI:
                ds.append({"ma": f"SJC{x['Id']}", "ten": SJC_LOAI[x["Id"]], "dv": "triệu đồng/lượng",
                           "mua": x["BuyValue"] / 1e6, "ban": x["SellValue"] / 1e6})
    except Exception as e:
        log.warning("Không lấy được giá vàng SJC: %s", str(e)[:80])
    if not ds:
        # SJC chặn máy chủ GitHub (403): dùng bảng giá vàng CafeF, giá theo nghìn đồng/chỉ
        try:
            r = requests.get("https://cafef.vn/du-lieu/Ajax/ajaxgoldprice.ashx", params={"index": 11},
                             headers=UA, timeout=20)
            r.raise_for_status()
            theo_ten = {x["name"]: x for x in r.json().get("Data") or []}
            for ten_cafef, ma, ten in [("Vàng miếng SJC 999.9", "SJC1", "Vàng SJC miếng"),
                                       ("Nhẫn Trơn PNJ 999.9", "NHAN_PNJ", "Vàng nhẫn PNJ 999.9")]:
                if ten_cafef in theo_ten:
                    x = theo_ten[ten_cafef]
                    ds.append({"ma": ma, "ten": ten, "dv": "triệu đồng/lượng · theo CafeF",
                               "mua": x["buyPrice"] / 100, "ban": x["sellPrice"] / 100})
        except Exception as e:
            log.warning("Không lấy được giá vàng từ CafeF: %s", str(e)[:80])
    try:
        r = requests.get("https://portal.vietcombank.com.vn/Usercontrols/TVPortal.TyGia/pXML.aspx",
                         headers=UA, timeout=20)
        r.raise_for_status()
        so = lambda s: float(s.replace(",", "")) if s and s != "-" else None
        ty_gia = {m[0]: m for m in re.findall(
            r'CurrencyCode="(\w+)"[^>]*Buy="([^"]*)"[^>]*Transfer="([^"]*)"[^>]*Sell="([^"]*)"', r.text)}
        for nt in VCB_NGOAI_TE:
            if nt in ty_gia:
                _, mua_tm, mua_ck, ban = ty_gia[nt]
                ds.append({"ma": nt, "ten": f"{nt}/VND", "dv": "Vietcombank, mua chuyển khoản",
                           "mua": so(mua_ck), "ban": so(ban)})
    except Exception as e:
        log.warning("Không lấy được tỷ giá Vietcombank: %s", str(e)[:80])
    hom_nay = datetime.now(VN_TZ).date().isoformat()
    for g in ds:
        if g["ban"] is None:
            continue
        con.execute("INSERT OR REPLACE INTO gia_tn VALUES (?,?,?)", (hom_nay, g["ma"], g["ban"]))
        truoc = con.execute("SELECT ban FROM gia_tn WHERE ma=? AND ngay<? ORDER BY ngay DESC LIMIT 1",
                            (g["ma"], hom_nay)).fetchone()
        g["pt"] = (g["ban"] / truoc[0] - 1) * 100 if truoc and truoc[0] else None
    con.commit()
    return {"ten": "Trong nước", "kieu": "mua_ban", "ds": ds} if ds else None


# ---- Tổng quan thị trường HOSE: độ rộng, top tăng/giảm (dữ liệu trang Thống kê của HOSE), VN-Index trong phiên ----
# Tạm tắt trên trang web (02/11/2026, theo yêu cầu); giữ hàm để bật lại: thêm "thi_truong" vào du_lieu trong xuat_html.
HOSE_MARKET = "https://api.hsx.vn/mk/api/v1/market/"


def lay_thi_truong(tat_ca_ma):
    so = lambda s: float(str(s).replace(",", ""))
    lay = lambda duong_dan: requests.get(HOSE_MARKET + duong_dan, headers=UA, timeout=20).json()["data"]
    try:
        # danh sách "top" xin 600 mã thì trả về đủ mọi mã tăng / giảm trong phiên
        tang = [x for x in lay("top-up-ratio-securities/600") if x["securitySymbol"] in tat_ca_ma]
        giam = [x for x in lay("top-down-ratio-securities/600") if x["securitySymbol"] in tat_ca_ma]
        tom_tat = lay("summary/hompage?type=VNINDEX")
    except Exception as e:
        log.warning("Không lấy được số liệu thị trường HOSE: %s", str(e)[:80])
        return None
    cp = lambda ds: [{"ma": x["securitySymbol"], "gia": so(x["closePrice"]), "pt": x["changePriceRatioValue"]}
                     for x in ds if isinstance(x["changePriceRatioValue"], (int, float))]   # bỏ mã mới niêm yết (Infinity)
    tang, giam = cp(tang), cp(giam)
    kq = {
        "do_rong": {"tang": len(tang), "giam": len(giam), "dung": max(0, len(tat_ca_ma) - len(tang) - len(giam))},
        "gtgd": so(tom_tat["gtgd"]), "klgd": so(tom_tat["klgd"]),
        "tang": sorted(tang, key=lambda x: -x["pt"])[:10], "giam": sorted(giam, key=lambda x: x["pt"])[:10],
    }
    try:
        r = requests.get("https://query1.finance.yahoo.com/v8/finance/chart/^VNINDEX.VN", headers=UA, timeout=15,
                         params={"range": "1d", "interval": "5m"})
        r.raise_for_status()
        k = r.json()["chart"]["result"][0]
        diem = [[t, round(c, 2)] for t, c in zip(k.get("timestamp") or [], k["indicators"]["quote"][0]["close"]) if c]
        kq["vnindex"] = {"gia": k["meta"].get("regularMarketPrice"), "truoc": k["meta"].get("chartPreviousClose"),
                         "cao": k["meta"].get("regularMarketDayHigh"), "thap": k["meta"].get("regularMarketDayLow"),
                         "diem": diem}
    except Exception as e:
        log.warning("Không lấy được VN-Index trong phiên: %s", str(e)[:80])
    return kq


# ---- Biểu đồ: giá vàng, lãi suất ----
BIG4 = {"AGB", "VCB", "BID", "CTG"}
# Máy chủ HNX gửi thiếu chứng chỉ trung gian (GlobalSign GCC R3 EV TLS CA 2025). Bổ sung đúng chứng chỉ đó
# (tải từ GlobalSign) vào bộ chứng chỉ gốc của certifi để vẫn xác thực HTTPS đầy đủ. Chứng chỉ hết hạn 07/2027.
CHUNG_CHI_HNX = THU_MUC / "chung_chi" / "globalsign_gcc_r3_ev_tls_ca_2025.pem"
_bo_chung_chi_hnx = None


def bo_chung_chi_hnx():
    global _bo_chung_chi_hnx
    if _bo_chung_chi_hnx is None:
        import certifi
        import tempfile
        duong_dan = Path(tempfile.gettempdir()) / "tin_tuc_ca_hnx.pem"
        duong_dan.write_text(Path(certifi.where()).read_text() + "\n" + CHUNG_CHI_HNX.read_text())
        _bo_chung_chi_hnx = str(duong_dan)
    return _bo_chung_chi_hnx


def lay_yahoo_ngay(ma, khoang="1y"):
    """[[ngày, giá đóng cửa]] theo ngày từ Yahoo Finance."""
    r = requests.get(f"https://query1.finance.yahoo.com/v8/finance/chart/{ma}", headers=UA, timeout=20,
                     params={"range": khoang, "interval": "1d"})
    r.raise_for_status()
    k = r.json()["chart"]["result"][0]
    return [[datetime.fromtimestamp(t, VN_TZ).date().isoformat(), round(c, 3)]
            for t, c in zip(k["timestamp"], k["indicators"]["quote"][0]["close"]) if c is not None]


def hnx_loi_suat(ngay):
    """Đường cong lợi suất TPCP của HNX ngày dd/mm/yyyy: [(kỳ hạn, par yield %)]. Ngày nghỉ thì rỗng."""
    r = requests.post("https://www.hnx.vn/ModuleReportBonds/Bond_YieldCurve/SearchAndNextPageYieldCurveData",
                      data={"pDate": ngay}, headers={**UA, "X-Requested-With": "XMLHttpRequest"}, timeout=20,
                      verify=bo_chung_chi_hnx())
    r.raise_for_status()
    txt = html.unescape(re.sub(r"<[^>]+>", "|", r.text))
    return [(f"{ky} {don_vi}", float(par.replace(",", ".")))
            for ky, don_vi, _, par in re.findall(r"(\d+)\s*(tháng|năm)\W+([\d,]+)\W+([\d,]+)", txt)]


def cap_nhat_tpcp(con):
    """Lợi suất TPCP VN 10 năm: lần đầu lấy bù 1 năm (mỗi tuần một mốc, tối đa 20 mốc/lần chạy), sau đó mỗi ngày.
    Trả về đường cong lợi suất mới nhất (các kỳ hạn) để vẽ."""
    hom_nay = datetime.now(VN_TZ).date()
    da_co = {r[0] for r in con.execute("SELECT ngay FROM chuoi WHERE ma='TPCP10'")}
    can = [hom_nay - timedelta(days=i) for i in range(0, 4)] + [hom_nay - timedelta(weeks=w) for w in range(1, 53)]
    lay_them = 0
    for d in can:
        if d.isoformat() in da_co or d.weekday() >= 5 or lay_them >= 20:
            continue
        try:
            ds = hnx_loi_suat(d.strftime("%d/%m/%Y"))
        except Exception as e:
            log.warning("Không lấy được lợi suất TPCP HNX: %s", str(e)[:80])
            break
        lay_them += 1
        if dict(ds).get("10 năm"):
            con.execute("INSERT OR REPLACE INTO chuoi VALUES ('TPCP10', ?, ?)", (d.isoformat(), dict(ds)["10 năm"]))
    con.commit()
    for i in range(0, 5):   # đường cong của ngày giao dịch gần nhất
        d = hom_nay - timedelta(days=i)
        if d.weekday() < 5:
            try:
                ds = hnx_loi_suat(d.strftime("%d/%m/%Y"))
                if ds:
                    return {"ngay": d.isoformat(), "ds": ds}
            except Exception:
                return None
    return None


# Các lần Vietcombank đổi lãi suất tiết kiệm 12 tháng (tại quầy) trước khi hệ thống tự đọc hằng ngày.
# Đối chiếu bản lưu trang lãi suất VCB trên web.archive.org (28/11/2025 4,6%; 18/01–11/03/2026 5,2%;
# 10/04–09/10/2026 5,9%; 24/10/2026 5,4%) với ngày điều chỉnh báo chí đưa tin (16/12/2025, 24/03/2026, 20/10/2026).
LS12_VCB_MOC = [("2025-12-16", 5.2), ("2026-03-24", 5.9), ("2026-10-20", 5.4)]


def lay_ls_vcb():
    """Lãi suất tiết kiệm 12 tháng tại quầy của Vietcombank, đọc trên bảng lãi suất vietcombank.com.vn."""
    h = requests.get("https://www.vietcombank.com.vn/vi-VN/KHCN/Cong-cu-Tien-ich/KHCN---Lai-suat", headers=UA, timeout=30).text
    d = json.loads(html.unescape(re.search(r'id="currentDataInterestRate" value="([^"]+)"', h).group(1)))
    x = next(x for x in d["Data"] if x["tenorType"] == "Savings" and x["tenor"] == "12-months" and x["currencyCode"] == "VND")
    return round(x["rates"] * 100, 2)


def lay_bieu_do(con):
    """Số liệu cho tab Biểu đồ. Mỗi phần lỗi riêng thì bỏ phần đó, không ảnh hưởng phần khác."""
    bd = {}
    try:   # giá vàng SJC 1 năm (CafeF), triệu đồng/lượng; giữ mốc mới nhất mỗi ngày
        r = requests.get("https://cafef.vn/du-lieu/Ajax/ajaxgoldpricehistory.ashx", params={"index": "1y"},
                         headers=UA, timeout=20)
        theo_ngay = {}
        for x in r.json()["Data"]["goldPriceWorldHistories"]:
            if x["name"] == "SJC":
                ngay = datetime.fromisoformat(x["createdAt"].replace("Z", "+00:00")).astimezone(VN_TZ).date().isoformat()
                theo_ngay.setdefault(ngay, [ngay, x["buyPrice"], x["sellPrice"]])
        bd["vang_sjc"] = sorted(theo_ngay.values())
    except Exception as e:
        log.warning("Không lấy được lịch sử giá vàng SJC: %s", str(e)[:80])
    for khoa, ma in (("vang_tg", "GC=F"), ("my_10n", "^TNX"), ("my_3t", "^IRX")):
        try:
            bd[khoa] = lay_yahoo_ngay(ma)
        except Exception as e:
            log.warning("Không lấy được lịch sử %s: %s", ma, str(e)[:80])
    try:   # lãi suất tiết kiệm: CafeF chỉ có số hiện tại, tự lưu mỗi ngày để thành biểu đồ
        r = requests.get("https://cafefnew.mediacdn.vn/Images/Uploaded/DuLieuDownload/Liveboard/all_banks_interest_rates.json",
                         headers=UA, timeout=20)
        bang = []
        for x in r.json()["Data"]:
            ls = {k["deposit"]: k["value"] for k in x["interestRates"]}
            if ls.get(12):
                bang.append({"ten": x["name"], "ma": x["symbol"], "t6": ls.get(6), "t12": ls.get(12), "t24": ls.get(24)})
        hom_nay = datetime.now(VN_TZ).date().isoformat()
        tb = lambda ds: round(sum(ds) / len(ds), 3) if ds else None
        for ma_chuoi, gia in (("TK12_TB", tb([b["t12"] for b in bang])),
                              ("TK12_BIG4", tb([b["t12"] for b in bang if b["ma"] in BIG4]))):
            if gia:
                con.execute("INSERT OR REPLACE INTO chuoi VALUES (?, ?, ?)", (ma_chuoi, hom_nay, gia))
        con.commit()
        bd["tk_bang"] = sorted(bang, key=lambda b: -b["t12"])
    except Exception as e:
        log.warning("Không lấy được lãi suất tiết kiệm: %s", str(e)[:80])
    try:   # Vietcombank 12 tháng từ đầu năm: mốc điều chỉnh đã biết + số đọc mỗi ngày, kéo giá trị qua từng ngày
        hom_nay = datetime.now(VN_TZ).date()
        con.execute("INSERT OR REPLACE INTO chuoi VALUES (?, ?, ?)", ("LS12_VCB", hom_nay.isoformat(), lay_ls_vcb()))
        con.execute("DELETE FROM chuoi WHERE ma LIKE 'LS12_%' AND ma != 'LS12_VCB'")
        con.commit()
        moc = sorted(LS12_VCB_MOC + [tuple(r) for r in con.execute("SELECT ngay, gia FROM chuoi WHERE ma='LS12_VCB'")])
        ngay, chuoi_vcb = date(hom_nay.year, 1, 1), []
        while ngay <= hom_nay:
            gia = [g for n, g in moc if n <= ngay.isoformat()]
            if gia:
                chuoi_vcb.append([ngay.isoformat(), gia[-1]])
            ngay += timedelta(days=1)
        bd["ls_vcb"] = {"t12": chuoi_vcb[-1][1], "chuoi": chuoi_vcb}
    except Exception as e:
        log.warning("Không lấy được lãi suất Vietcombank: %s", str(e)[:80])
    bd["tpcp_duong_cong"] = cap_nhat_tpcp(con)
    chuoi = lambda ma: [list(r) for r in con.execute("SELECT ngay, gia FROM chuoi WHERE ma=? ORDER BY ngay", (ma,))]
    bd["tk12_tb"], bd["tk12_big4"], bd["tpcp10"] = chuoi("TK12_TB"), chuoi("TK12_BIG4"), chuoi("TPCP10")
    return bd


# ---- KQKD quý toàn HOSE (số liệu báo cáo tài chính trên trang mã cổ phiếu của CafeF) ----
KQKD_MOI_LAN = 30   # số mã cập nhật mỗi lần chạy; ~400 mã HOSE quay vòng khoảng 2 giờ một lượt
RE_CONG_BO_BCTC = re.compile(r"báo cáo tài chính|bctc|kết quả kinh doanh|kqkd|giải trình", re.I)


def lay_kqkd_ma(ma):
    """(quý, doanh thu, doanh thu cùng kỳ, LNST cty mẹ, LNST cùng kỳ) của quý gần nhất, đơn vị nghìn đồng."""
    r = requests.get("https://cafef.vn/du-lieu/Ajax/PageNew/FinanceReport.ashx", headers=UA, timeout=20, params={
        "Type": 1, "Symbol": ma.lower(), "TotalRow": 5, "EndDate": "4-2030", "ReportType": "QUY", "Sort": "DESC"})
    ds = (r.json().get("Data") or {}).get("Value") or []
    if not ds:
        return None
    gia_tri = lambda q: {v["Code"]: v["Value"] for v in q["Value"]}
    moi = ds[0]
    ck = next((q for q in ds if q["Year"] == moi["Year"] - 1 and q["Quater"] == moi["Quater"]), None)
    a, b = gia_tri(moi), gia_tri(ck) if ck else {}
    dt = lambda g: g.get("DTTBHCCDV", g.get("TotalIncome"))   # ngân hàng, bảo hiểm dùng "Tổng doanh thu"
    return f"{moi['Year']}-Q{moi['Quater']}", dt(a), dt(b), a.get("NetIncome"), b.get("NetIncome")


def cap_nhat_kqkd(con, tat_ca_ma):
    """Ưu tiên mã vừa có công bố BCTC/KQKD trên HOSE, còn lại quay vòng mã lâu chưa cập nhật nhất."""
    da_co = {r["ma"]: r["cap_nhat"] for r in con.execute("SELECT ma, cap_nhat FROM kqkd")}
    uu_tien = [r["ma"] for r in con.execute(
        "SELECT ma, tieu_de, MAX(thoi_gian) t FROM cong_bo GROUP BY ma ORDER BY t DESC LIMIT 60")
        if r["ma"] in tat_ca_ma and RE_CONG_BO_BCTC.search(r["tieu_de"]) and (da_co.get(r["ma"]) or "") < r["t"]]
    con_lai = sorted(tat_ca_ma - set(uu_tien), key=lambda m: da_co.get(m) or "")
    bay_gio = datetime.now(timezone.utc).isoformat()
    moi = 0
    for ma in (uu_tien + con_lai)[:KQKD_MOI_LAN]:
        try:
            kq = lay_kqkd_ma(ma)
        except Exception as e:
            log.warning("Không lấy được KQKD %s: %s", ma, str(e)[:60])
            continue
        if not kq:
            con.execute("INSERT OR REPLACE INTO kqkd (ma, cap_nhat) VALUES (?, ?)", (ma, bay_gio))
            continue
        cu = con.execute("SELECT quy, phat_hien FROM kqkd WHERE ma=?", (ma,)).fetchone()
        cung_quy = cu is not None and cu[0] == kq[0]
        moi += not cung_quy
        con.execute("INSERT OR REPLACE INTO kqkd VALUES (?,?,?,?,?,?,?,?)",
                    (ma, *kq, cu[1] if cung_quy else bay_gio, bay_gio))   # phat_hien: lần đầu thấy số quý này
    con.commit()
    if moi:
        log.info("KQKD: %d mã có số liệu quý mới", moi)


def du_lieu_kqkd(con, tat_ca_ma):
    """Quý đang trong mùa công bố và danh sách mã đã có số quý đó. Quý được chọn là quý mới nhất có từ 10% số mã
    đã quét trở lên (bỏ qua vài công ty có năm tài chính lệch, vd đã ghi "Q4" khi mọi người đang công bố Q3)."""
    dem = con.execute("SELECT quy, COUNT(*) FROM kqkd WHERE quy IS NOT NULL GROUP BY quy ORDER BY quy DESC").fetchall()
    tong = sum(r[1] for r in dem)
    quy = next((r[0] for r in dem if r[1] >= max(3, tong * 0.1)), dem[0][0] if dem else None)
    if not quy:
        return None
    pt = lambda a, b: round((a / b - 1) * 100, 1) if a is not None and b and b > 0 else None
    ds = [{"ma": r["ma"], "dt": r["dt"], "dt_pt": pt(r["dt"], r["dt_ck"]), "ln": r["ln"], "ln_pt": pt(r["ln"], r["ln_ck"]),
           "ln_ck": r["ln_ck"], "t": r["phat_hien"]}
          for r in con.execute("SELECT * FROM kqkd WHERE quy=?", (quy,))]
    return {"quy": quy, "tong": len(tat_ca_ma), "da_quet": con.execute("SELECT COUNT(*) FROM kqkd").fetchone()[0], "ds": ds}


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
        "gia": {**({"tn": tn} if (tn := lay_gia_trong_nuoc(con)) else {}), **lay_bang_gia()},
        "bot": ten_bot(con, cfg),
        "bieu_do": lay_bieu_do(con),
        "kqkd": du_lieu_kqkd(con, doc_ma()),
        "cong_bo": [{"t": r["thoi_gian"], "ma": r["ma"], "td": r["tieu_de"], "link": r["link"]}
                    for r in con.execute("SELECT * FROM cong_bo WHERE thoi_gian>=? ORDER BY thoi_gian DESC LIMIT 400", (
                        (datetime.now(timezone.utc) - timedelta(days=NGAY_CONG_BO_HTML)).isoformat(),))],
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
    thu_tu = ["uu", "ck", "dn", "vm", "bds", "cg", "hh", "qt"]   # cùng thứ tự với các tab trên trang web
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


# ---- Bot Telegram cho người xem: mỗi người tự lập danh mục mã và nhận thông báo riêng ----
# Lệnh: /theodoi HPG FPT, /bo FPT, /danhmuc, /huy. Bot đọc lệnh mỗi lần hệ thống chạy (~10 phút), nên trả lời trễ
# tối đa chừng đó. chat_id và danh mục của người xem chỉ nằm trong kho dữ liệu (bộ nhớ đệm GitHub), không đưa lên repo.
TOI_DA_MA_MOI_NGUOI = 30
HUONG_DAN_BOT = (
    "Các lệnh:\n"
    "/theodoi HPG FPT MWG — thêm mã vào danh mục\n"
    "/bo FPT — bỏ mã\n"
    "/danhmuc — xem danh mục\n"
    "/huy — xóa danh mục, ngừng nhận thông báo\n\n"
    "Khi mã trong danh mục có tin tức, công bố thông tin HOSE, báo cáo định giá của CTCK hoặc KQKD quý mới, "
    "bot sẽ nhắn riêng cho bạn (kiểm tra khoảng 10 phút một lần, không gửi từ 23h đến 6h).")


def goi_bot(cfg, phuong_thuc, **tham_so):
    token = cfg.get("telegram", "token", fallback="").strip()
    if not token:
        return None
    r = requests.post(f"https://api.telegram.org/bot{token}/{phuong_thuc}", data=tham_so, timeout=20)
    if not r.ok:
        log.warning("Bot %s lỗi %s: %s", phuong_thuc, r.status_code, r.text[:150])
        return None
    return r.json().get("result")


def nhan_tin(cfg, chat_id, text):
    return goi_bot(cfg, "sendMessage", chat_id=chat_id, text=text, parse_mode="HTML",
                   disable_web_page_preview="true") is not None


def cau_hinh(con, khoa, gia_tri=None):
    """Đọc (gia_tri=None) hoặc ghi một giá trị trong bảng cau_hinh."""
    if gia_tri is None:
        r = con.execute("SELECT gia_tri FROM cau_hinh WHERE khoa=?", (khoa,)).fetchone()
        return r[0] if r else None
    con.execute("INSERT OR REPLACE INTO cau_hinh VALUES (?, ?)", (khoa, str(gia_tri)))
    con.commit()


def ten_bot(con, cfg):
    """Tên bot (vd tinck_dat_bot) để trang web tạo nút mở bot. Lần đầu cũng đăng ký menu lệnh cho bot."""
    ten = cau_hinh(con, "bot_ten")
    if not ten:
        toi = goi_bot(cfg, "getMe")
        if toi:
            ten = toi.get("username")
            cau_hinh(con, "bot_ten", ten)
            goi_bot(cfg, "setMyCommands", commands=json.dumps([
                {"command": "theodoi", "description": "Thêm mã vào danh mục, vd /theodoi HPG FPT"},
                {"command": "bo", "description": "Bỏ mã khỏi danh mục, vd /bo FPT"},
                {"command": "danhmuc", "description": "Xem danh mục đang theo dõi"},
                {"command": "huy", "description": "Xóa danh mục, ngừng nhận thông báo"}]))
    return ten


def danh_muc_cua(con, chat_id):
    return [r[0] for r in con.execute("SELECT ma FROM theo_doi WHERE chat_id=? ORDER BY ma", (chat_id,))]


def xu_ly_lenh_bot(con, cfg, tat_ca_ma):
    """Đọc tin nhắn người xem gửi cho bot (getUpdates) và cập nhật danh mục của từng người."""
    offset = int(cau_hinh(con, "bot_offset") or 0)
    cap_nhat = goi_bot(cfg, "getUpdates", offset=offset + 1 if offset else "", timeout=0,
                       allowed_updates='["message"]')
    if not cap_nhat:
        return
    bay_gio = datetime.now(timezone.utc)
    for u in cap_nhat:
        offset = max(offset, u["update_id"])
        m = u.get("message") or {}
        chat = m.get("chat") or {}
        if chat.get("type") != "private" or "text" not in m:
            continue
        if bay_gio.timestamp() - m.get("date", 0) > 86400:   # tin nhắn quá 1 ngày (vd lúc mới bật tính năng): bỏ qua
            continue
        chat_id = str(chat["id"])
        tu = m["text"].replace(",", " ").split()
        lenh = tu[0].split("@")[0].lower() if tu else ""
        ma_nhap = [x.strip().upper() for x in re.split(r"[\s_\-]+", " ".join(tu[1:])) if x.strip()]
        if lenh.startswith("/") is False and tu and all(x.upper() in tat_ca_ma for x in tu):
            lenh, ma_nhap = "/theodoi", [x.upper() for x in tu]   # nhắn thẳng "HPG FPT" cũng được
        con.execute("INSERT OR IGNORE INTO nguoi_dung VALUES (?, ?, ?, ?)",
                    (chat_id, chat.get("first_name") or chat.get("username") or "", bay_gio.isoformat(), bay_gio.isoformat()))
        if lenh in ("/start", "/theodoi", "/them") and ma_nhap:
            hop_le = [x for x in dict.fromkeys(ma_nhap) if x in tat_ca_ma]
            sai = [x for x in ma_nhap if x not in tat_ca_ma]
            dang_co = danh_muc_cua(con, chat_id)
            them = [x for x in hop_le if x not in dang_co][:max(0, TOI_DA_MA_MOI_NGUOI - len(dang_co))]
            con.executemany("INSERT OR IGNORE INTO theo_doi VALUES (?, ?)", [(chat_id, x) for x in them])
            tra_loi = (f"✅ Đã thêm: {', '.join(them)}\n" if them else "") + \
                      (f"⚠️ Không có trong danh sách cổ phiếu HOSE: {', '.join(sai)}\n" if sai else "") + \
                      f"\n⭐ Danh mục của bạn: {', '.join(danh_muc_cua(con, chat_id)) or '(trống)'}"
        elif lenh in ("/bo", "/xoa") and ma_nhap:
            con.executemany("DELETE FROM theo_doi WHERE chat_id=? AND ma=?", [(chat_id, x) for x in ma_nhap])
            tra_loi = f"Đã bỏ: {', '.join(ma_nhap)}\n⭐ Danh mục của bạn: {', '.join(danh_muc_cua(con, chat_id)) or '(trống)'}"
        elif lenh == "/danhmuc":
            tra_loi = f"⭐ Danh mục của bạn: {', '.join(danh_muc_cua(con, chat_id)) or '(trống)'}\n\n{HUONG_DAN_BOT}"
        elif lenh in ("/huy", "/stop"):
            con.execute("DELETE FROM theo_doi WHERE chat_id=?", (chat_id,))
            tra_loi = "Đã xóa danh mục, bạn sẽ không nhận thông báo nữa. Gửi /theodoi kèm mã để theo dõi lại."
        elif lenh == "/start":
            tra_loi = f"Chào bạn! Đây là bot Bản Tin Tự Động - Đạt VCBS.\n\n{HUONG_DAN_BOT}"
        else:
            tra_loi = HUONG_DAN_BOT
        con.commit()
        nhan_tin(cfg, chat_id, html.escape(tra_loi))
    cau_hinh(con, "bot_offset", offset)


def gui_thong_bao_danh_muc(con, cfg):
    """Nhắn riêng từng người xem: tin, công bố, báo cáo CTCK, KQKD mới của các mã trong danh mục của họ."""
    bay_gio = datetime.now(timezone.utc).isoformat()
    for nguoi in con.execute("SELECT * FROM nguoi_dung").fetchall():
        dm = set(danh_muc_cua(con, nguoi["chat_id"]))
        if not dm:
            continue
        moc = nguoi["moc"]
        theo_ma = {m: [] for m in sorted(dm)}
        for r in con.execute("SELECT * FROM tin WHERE giu=1 AND lay_luc>? AND lay_luc<=? ORDER BY thoi_gian", (moc, bay_gio)):
            trung = [m for m in r["ma"].split(",") if m in dm]
            if trung:
                nguon = r["nguon"] + (" · dịch máy" if r["dich"] == 1 else "")
                theo_ma[trung[0]].append(f"📰 <a href=\"{html.escape(r['link'])}\">{html.escape(r['tieu_de'])}</a> <i>({html.escape(nguon)})</i>")
        for r in con.execute("SELECT * FROM cong_bo WHERE lay_luc>? AND lay_luc<=? ORDER BY thoi_gian", (moc, bay_gio)):
            if r["ma"] in dm:
                theo_ma[r["ma"]].append(f"📢 Công bố HOSE: <a href=\"{html.escape(r['link'])}\">{html.escape(r['tieu_de'])}</a>")
        for r in con.execute("SELECT * FROM bao_cao WHERE lay_luc>? AND lay_luc<=?", (moc, bay_gio)):
            if r["ma"] in dm:
                them = " · ".join(x for x in [r["ctck_ngan"], r["khuyen_nghi"],
                                              f"GMT {r['gia_muc_tieu']:,.0f}".replace(",", ".") if r["gia_muc_tieu"] else ""] if x)
                theo_ma[r["ma"]].append(f"📊 {html.escape(them)}: <a href=\"{html.escape(r['link'])}\">{html.escape(r['tieu_de'])}</a>")
        for r in con.execute("SELECT * FROM kqkd WHERE phat_hien>? AND phat_hien<=?", (moc, bay_gio)):
            if r["ma"] in dm and r["quy"]:
                pt = lambda a, b: f" ({(a / b - 1) * 100:+.1f}%)".replace(".", ",") if a is not None and b and b > 0 else ""
                ty = lambda x: f"{x / 1e6:,.1f}".replace(",", "X").replace(".", ",").replace("X", ".") if x is not None else "–"
                nam, q = r["quy"].split("-Q")
                theo_ma[r["ma"]].append(f"📑 KQKD quý {q}/{nam}: doanh thu {ty(r['dt'])} tỷ{pt(r['dt'], r['dt_ck'])}, "
                                        f"LNST cty mẹ {ty(r['ln'])} tỷ{pt(r['ln'], r['ln_ck'])}")
        dong = [f"<b>⭐ Danh mục của bạn có tin mới</b>"]
        for m, ds in theo_ma.items():
            if ds:
                dong += ["", f"<b>{m}</b>"] + [f"• {x}" for x in ds]
        if len(dong) > 1:
            tin_nhan, hien_tai = [], ""
            for d in dong:
                if len(hien_tai) + len(d) + 1 > 3900:
                    tin_nhan.append(hien_tai)
                    hien_tai = ""
                hien_tai += d + "\n"
            tin_nhan.append(hien_tai)
            if not all(nhan_tin(cfg, nguoi["chat_id"], t) for t in tin_nhan):
                continue   # gửi lỗi: giữ mốc cũ, lần sau gửi lại
        con.execute("UPDATE nguoi_dung SET moc=? WHERE chat_id=?", (bay_gio, nguoi["chat_id"]))
        con.commit()


def chay(cfg):
    tat_ca_ma = doc_ma()          # HOSE: bảng KQKD, công bố thông tin
    ma_gan = doc_ma_gan()         # HOSE + HNX: gắn mã cho tin, lệnh theo dõi của bot
    con = mo_db()
    con.row_factory = sqlite3.Row
    lan_dau = con.execute("SELECT COUNT(*) FROM tin").fetchone()[0] == 0
    try:
        xu_ly_lenh_bot(con, cfg, ma_gan)   # trả lời lệnh của người xem cả trong giờ yên lặng
    except Exception:
        log.exception("Lỗi xử lý lệnh bot")
    tin = thu_thap(ma_gan)
    moi = luu(con, tin)
    log.info("Đọc %d tin, %d tin mới", len(tin), moi)
    con.execute("DELETE FROM tin WHERE thoi_gian < ?",
                ((datetime.now(timezone.utc) - timedelta(days=XOA_SAU_NGAY)).isoformat(),))
    con.commit()
    dich_tin_nuoc_ngoai(con)
    phan_loai_lai(con, ma_gan, doc_ten_goi())
    lay_bao_cao_ctck(con)
    lay_cong_bo(con)
    cap_nhat_kqkd(con, tat_ca_ma)
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
    try:
        gui_thong_bao_danh_muc(con, cfg)
    except Exception:
        log.exception("Lỗi gửi thông báo danh mục")

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

    # Công bố thông tin: chỉ gửi mã cổ phiếu HOSE trong ma_hose.csv (bỏ ETF, chứng quyền...)
    cong_bo = con.execute("SELECT * FROM cong_bo WHERE da_gui=0 ORDER BY thoi_gian").fetchall()
    if cong_bo:
        gui = cfg.get("cai_dat", "gui_cong_bo", fallback="yes").strip().lower() != "no"
        can_gui = [r for r in cong_bo if r["ma"] in tat_ca_ma] if gui else []
        for i in range(0, len(can_gui), 20):
            if not gui_telegram(cfg, soan_cong_bo(can_gui[i:i + 20], uu_tien)):
                return
        con.execute("UPDATE cong_bo SET da_gui=1 WHERE da_gui=0")
        con.commit()
        if can_gui:
            log.info("Đã gửi %d công bố thông tin", len(can_gui))

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
    tin = thu_thap(doc_ma_gan())
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
