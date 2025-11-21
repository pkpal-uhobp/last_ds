import sys
import secrets
import math
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout, QTabWidget,
    QPushButton, QTextEdit, QLabel, QLineEdit, QFileDialog, QComboBox,
    QGroupBox, QMessageBox, QSplitter, QSpinBox, QFrame, QMenuBar
)
from PySide6.QtCore import Qt
from PySide6.QtGui import QFont, QPalette, QColor, QAction

# ===========================
# Ограничения по методам
# ===========================
METHOD_MAX_BITS = {
    "miller-rabin": 1024,
    "trial": 32,
    "sieve": 20,
    "genpr": 24
}

# RSA Constants
RSA_MIN_BITS = 8
RSA_MAX_BITS = 128
RSA_MAX_GENERATION_ATTEMPTS = 20
RSA_COMMON_E_VALUES = [3, 5, 17, 257, 65537]
RSA_MSG_TRUNCATE_SHORT = 50
RSA_MSG_TRUNCATE_LONG = 100

# ===========================
# Генераторы гаммы
# ===========================
class LCG:
    def __init__(self, seed, a=1664525, b=1013904223, m=2 ** 32):
        if b % 2 == 0:
            raise ValueError("LCG: b должно быть нечётным (по Кнуту)")
        if a % 4 != 1:
            raise ValueError("LCG: a ≡ 1 (mod 4)")
        self.state = seed % m
        self.a = a
        self.b = b
        self.m = m
    def next(self):
        self.state = (self.a * self.state + self.b) % self.m
        return self.state

class Multiplicative:
    def __init__(self, seed, a=16807, m=2 ** 31 - 1):
        if seed == 0:
            raise ValueError("Мультипликативный генератор: seed ≠ 0")
        self.state = seed % m
        self.a = a
        self.m = m
    def next(self):
        self.state = (self.a * self.state) % self.m
        return self.state

class Additive:
    def __init__(self, seed1, seed2=None, m=2 ** 32):
        self.x = seed1 % m
        self.y = (seed2 or (seed1 * 1103515245 + 12345)) % m
        self.m = m
    def next(self):
        z = (self.x + self.y) % self.m
        self.x, self.y = self.y, z
        return z

def apply_gamma(data_bytes, gen):
    result = bytearray()
    block_size = 8
    for i in range(0, len(data_bytes), block_size):
        block = data_bytes[i:i + block_size]
        gamma = bytearray(gen.next() & 0xFF for _ in range(len(block)))
        encrypted = bytearray(b ^ g for b, g in zip(block, gamma))
        result.extend(encrypted)
    return bytes(result)

# ===========================
# Простые числа / тесты
# ===========================
_SMALL_PRIMES = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
for n in range(101, 1000, 2):
    if all(n % p for p in _SMALL_PRIMES if p * p <= n):
        _SMALL_PRIMES.append(n)

def is_prime_deterministic(n):
    if n < 2: return False
    for p in _SMALL_PRIMES:
        if n % p == 0:
            return n == p
    d = n - 1; s = 0
    while d % 2 == 0:
        d //= 2; s += 1
    for a in [2,325,9375,28178,450775,9780504,1795265022]:
        if a % n == 0: continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1: continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else: return False
    return True

def is_prime_miller_rabin(n, k=10):
    if n < 2: return False
    for p in _SMALL_PRIMES[:15]:
        if n % p == 0: return n == p
    d = n - 1; s = 0
    while d % 2 == 0:
        d //= 2; s += 1
    for _ in range(k):
        a = secrets.randbelow(n - 3) + 2
        x = pow(a, d, n)
        if x == 1 or x == n - 1: continue
        for __ in range(s - 1):
            x = (x * x) % n
            if x == n - 1: break
        else: return False
    return True

def genpr_algorithm(m, k):
    if m % 2 == 0: m += 1
    A = [1]*k
    d = 3
    while d * d <= m + 2*k - 2:
        r = m % d
        if r == 0:
            j = 0
        else:
            inv2 = pow(2, -1, d)
            j = ((-r)*inv2) % d
        jj = j
        while jj < k:
            if m + 2*jj != d:
                A[jj] = 0
            jj += d
        d = d + 4 if d % 6 == 1 else d + 2
    primes = []
    for i in range(k):
        if A[i]:
            cand = m + 2*i
            if cand >= 2 and is_prime_deterministic(cand):
                primes.append(cand)
    return primes

def generate_large_prime(bits, method='miller-rabin'):
    if bits < 2:
        raise ValueError("Битность ≥ 2")
    max_allowed = METHOD_MAX_BITS.get(method, 1024)
    if bits > max_allowed:
        raise ValueError(f"Метод '{method}' поддерживает ≤ {max_allowed} бит.")
    while True:
        candidate = secrets.randbits(bits)
        candidate |= (1 << (bits - 1)) | 1
        if any(candidate % p == 0 and candidate != p for p in _SMALL_PRIMES):
            continue
        if method == 'trial':
            if candidate < 2 or candidate % 2 == 0: continue
            limit = int(math.isqrt(candidate))
            f = 3
            while f <= limit and candidate % f:
                f += 2
            if f > limit: return candidate
        elif method == 'sieve':
            limit = (1 << bits) - 1
            sieve = [True]*(limit+1)
            sieve[0:2] = [False, False]
            for i in range(2, int(limit**0.5)+1):
                if sieve[i]:
                    sieve[i*i::i] = [False]*((limit - i*i)//i + 1)
            primes = [i for i, fl in enumerate(sieve) if fl]
            if primes: return secrets.choice(primes)
        elif method == 'genpr':
            m = 1 << (bits - 1)
            if m % 2 == 0: m += 1
            k = (1 << (bits - 1)) // 2
            primes = genpr_algorithm(m, k)
            if primes: return secrets.choice(primes)
        elif method == 'miller-rabin':
            if candidate < (1 << 64):
                if is_prime_deterministic(candidate):
                    return candidate
            else:
                if is_prime_miller_rabin(candidate, k=10):
                    return candidate

def mod_exp(base, exp, mod):
    if mod == 1: return 0
    result = 1
    base %= mod
    while exp > 0:
        if exp & 1:
            result = (result * base) % mod
        exp >>= 1
        base = (base * base) % mod
    return result

# ===========================
# Вкладка 1: Гаммирование
# ===========================
class GammaTab(QWidget):
    def __init__(self):
        super().__init__()
        layout = QVBoxLayout(self)

        top_bar = QHBoxLayout()
        self.btn_load = QPushButton("📂 Загрузить файл (.txt)")
        self.btn_load.clicked.connect(self.load_file)
        top_bar.addWidget(self.btn_load)
        top_bar.addStretch()
        layout.addLayout(top_bar)

        splitter = QSplitter(Qt.Horizontal)
        layout.addWidget(splitter)

        left_group = QGroupBox("Исходные данные")
        left_layout = QVBoxLayout(left_group)
        self.input_text = QTextEdit()
        self.input_text.setPlaceholderText("Введите текст или загрузите файл...")
        left_layout.addWidget(self.input_text)
        splitter.addWidget(left_group)

        right_group = QGroupBox("Результат (hex / текст)")
        right_layout = QVBoxLayout(right_group)
        self.output_text = QTextEdit()
        self.output_text.setReadOnly(True)
        right_layout.addWidget(self.output_text)
        splitter.addWidget(right_group)

        params_group = QGroupBox("Параметры гаммирования")
        params_layout = QVBoxLayout()

        seed_layout = QHBoxLayout()
        seed_layout.addWidget(QLabel("Seed (ключ):"))
        self.seed_input = QLineEdit("12345")
        self.bits_combo = QComboBox()
        self.bits_combo.addItems(["32", "64", "128", "256"])
        self.bits_combo.setCurrentText("128")
        self.btn_gen_seed = QPushButton("🎲 Сгенерировать")
        self.btn_gen_seed.clicked.connect(self.generate_seed)
        seed_layout.addWidget(self.seed_input)
        seed_layout.addWidget(QLabel("бит:"))
        seed_layout.addWidget(self.bits_combo)
        seed_layout.addWidget(self.btn_gen_seed)
        params_layout.addLayout(seed_layout)

        gen_layout = QHBoxLayout()
        gen_layout.addWidget(QLabel("Генератор гаммы:"))
        self.gen_combo = QComboBox()
        self.gen_combo.addItems([
            "Линейный конгруэнтный (LCG)",
            "Мультипликативный",
            "Аддитивный (Фибоначчи)"
        ])
        gen_layout.addWidget(self.gen_combo)
        params_layout.addLayout(gen_layout)

        params_group.setLayout(params_layout)
        layout.addWidget(params_group)

        btns_layout = QHBoxLayout()
        self.btn_encrypt = QPushButton("🔒 Зашифровать")
        self.btn_decrypt = QPushButton("🔓 Расшифровать")
        self.btn_encrypt.clicked.connect(self.encrypt)
        self.btn_decrypt.clicked.connect(self.decrypt)
        btns_layout.addWidget(self.btn_encrypt)
        btns_layout.addWidget(self.btn_decrypt)
        layout.addLayout(btns_layout)

        self.btn_save = QPushButton("💾 Сохранить результат")
        self.btn_save.clicked.connect(self.save_result)
        layout.addWidget(self.btn_save)

    def generate_seed(self):
        try:
            n_bits = int(self.bits_combo.currentText())
            seed = secrets.randbits(n_bits)
            self.seed_input.setText(str(seed))
        except Exception as e:
            QMessageBox.critical(self, "❌ Ошибка", f"Генерация seed:\n{e}")

    def load_file(self):
        path, _ = QFileDialog.getOpenFileName(self, "Открыть TXT", "", "Text Files (*.txt)")
        if path:
            try:
                with open(path, 'r', encoding='utf-8') as f:
                    self.input_text.setPlainText(f.read())
            except Exception as e:
                QMessageBox.critical(self, "❌ Ошибка", f"Чтение файла:\n{e}")

    def get_generator(self):
        seed = int(self.seed_input.text())
        typ = self.gen_combo.currentIndex()
        if typ == 0: return LCG(seed)
        if typ == 1: return Multiplicative(seed)
        return Additive(seed, seed + 1)

    def encrypt(self):
        try:
            text = self.input_text.toPlainText()
            if not text:
                raise ValueError("Введите текст")
            gen = self.get_generator()
            enc = apply_gamma(text.encode('utf-8'), gen)
            self.output_text.setPlainText(enc.hex())
            QMessageBox.information(self, "✅ Успех", "Текст зашифрован (HEX справа).")
        except Exception as e:
            QMessageBox.critical(self, "❌ Шифрование", str(e))

    def decrypt(self):
        try:
            txt = self.input_text.toPlainText()
            if not txt:
                raise ValueError("Введите шифротекст (hex или текст)")
            try:
                data = bytes.fromhex(txt)
            except ValueError:
                data = txt.encode('utf-8')
            gen = self.get_generator()
            dec = apply_gamma(data, gen)
            self.output_text.setPlainText(dec.decode('utf-8', errors='replace'))
            QMessageBox.information(self, "✅ Успех", "Текст расшифрован.")
        except Exception as e:
            QMessageBox.critical(self, "❌ Дешифрование", str(e))

    def save_result(self):
        text = self.output_text.toPlainText()
        if not text:
            QMessageBox.warning(self, "⚠️ Пусто", "Нет данных для сохранения.")
        else:
            path, _ = QFileDialog.getSaveFileName(self, "Сохранить", "", "Text Files (*.txt)")
            if path:
                try:
                    with open(path, 'w', encoding='utf-8') as f:
                        f.write(text)
                    QMessageBox.information(self, "✅ Сохранено", f"Файл:\n{path}")
                except Exception as e:
                    QMessageBox.critical(self, "❌ Ошибка", f"Запись:\n{e}")

# ===========================
# Вкладка 2: Модулярная арифметика
# ===========================
class ModArithmeticTab(QWidget):
    def __init__(self):
        super().__init__()
        layout = QVBoxLayout(self)

        params_group = QGroupBox("Генерация двух простых чисел")
        params_layout = QHBoxLayout()
        params_layout.addWidget(QLabel("Битность:"))
        self.bits_spin = QSpinBox()
        self.bits_spin.setRange(8, 1024)
        self.bits_spin.setValue(128)
        params_layout.addWidget(self.bits_spin)
        params_layout.addWidget(QLabel("Метод:"))
        self.method_combo = QComboBox()
        self.method_combo.addItems([
            "Миллер–Рабин (рекомендуется)",
            "Перебор (до 32 бит)",
            "Решето Эратосфена (до 20 бит)",
            "GENPR (до 24 бит)"
        ])
        self.method_combo.currentIndexChanged.connect(self.adjust_bits_limit)
        params_layout.addWidget(self.method_combo)
        self.btn_gen = QPushButton("🎲 Сгенерировать 2 простых")
        self.btn_gen.clicked.connect(self.generate_primes)
        params_layout.addWidget(self.btn_gen)
        params_group.setLayout(params_layout)
        layout.addWidget(params_group)

        primes_layout = QHBoxLayout()
        self.p1_edit = QLineEdit(); self.p1_edit.setPlaceholderText("p1")
        self.p2_edit = QLineEdit(); self.p2_edit.setPlaceholderText("p2")
        primes_layout.addWidget(self.p1_edit); primes_layout.addWidget(self.p2_edit)
        layout.addLayout(primes_layout)

        ops_group = QGroupBox("Операции: a, b, n, m")
        ops_layout = QVBoxLayout()
        row1 = QHBoxLayout()
        row1.addWidget(QLabel("a =")); self.a_edit = QLineEdit(); row1.addWidget(self.a_edit)
        row1.addWidget(QLabel("b =")); self.b_edit = QLineEdit(); row1.addWidget(self.b_edit)
        ops_layout.addLayout(row1)
        row2 = QHBoxLayout()
        row2.addWidget(QLabel("n =")); self.n_edit = QLineEdit("17"); row2.addWidget(self.n_edit)
        row2.addWidget(QLabel("m =")); self.m_edit = QLineEdit("101"); row2.addWidget(self.m_edit)
        ops_layout.addLayout(row2)
        ops_group.setLayout(ops_layout)
        layout.addWidget(ops_group)

        btns_layout = QHBoxLayout()
        self.btn_use = QPushButton("→ Использовать p1, p2 как a, b")
        self.btn_calc = QPushButton("🔢 Выполнить операции")
        self.btn_use.clicked.connect(self.use_primes)
        self.btn_calc.clicked.connect(self.calculate_all)
        btns_layout.addWidget(self.btn_use); btns_layout.addWidget(self.btn_calc)
        layout.addLayout(btns_layout)

        self.results = QTextEdit()
        self.results.setReadOnly(True)
        self.results.setPlaceholderText("Результаты...")
        layout.addWidget(self.results)

        footer = QHBoxLayout()
        self.btn_export = QPushButton("💾 Сохранить")
        self.btn_clear = QPushButton("🗑 Очистить")
        self.btn_export.clicked.connect(self.export)
        self.btn_clear.clicked.connect(self.results.clear)
        footer.addWidget(self.btn_export); footer.addWidget(self.btn_clear)
        layout.addLayout(footer)

    def adjust_bits_limit(self):
        method = self.get_method()
        max_bits = METHOD_MAX_BITS.get(method, 1024)
        if self.bits_spin.value() > max_bits:
            self.bits_spin.setValue(max_bits)
            QMessageBox.information(self, "ℹ️ Ограничение",
                                    f"Для метода '{method}' максимум {max_bits} бит. Скорректировано.")
        self.bits_spin.setMaximum(max_bits)

    def get_method(self):
        t = self.method_combo.currentText()
        if "Миллер" in t: return "miller-rabin"
        if "Перебор" in t: return "trial"
        if "Решето" in t: return "sieve"
        if "GENPR" in t: return "genpr"
        return "miller-rabin"

    def generate_primes(self):
        try:
            bits = self.bits_spin.value()
            method = self.get_method()
            p1 = generate_large_prime(bits, method)
            p2 = generate_large_prime(bits, method)
            while p1 == p2:
                p2 = generate_large_prime(bits, method)
            self.p1_edit.setText(str(p1))
            self.p2_edit.setText(str(p2))
            QMessageBox.information(self, "✅ Успех",
                                    f"Сгенерированы два простых по {bits} бит (метод: {method}).")
        except Exception as e:
            QMessageBox.critical(self, "❌ Генерация", str(e))

    def use_primes(self):
        try:
            p1 = self.p1_edit.text(); p2 = self.p2_edit.text()
            if not p1 or not p2:
                raise ValueError("Сначала сгенерируйте простые.")
            self.a_edit.setText(p1); self.b_edit.setText(p2)
        except Exception as e:
            QMessageBox.warning(self, "⚠️ Ошибка", str(e))

    def calculate_all(self):
        try:
            a = int(self.a_edit.text()); b = int(self.b_edit.text())
            n = int(self.n_edit.text()); m = int(self.m_edit.text())
            if b == 0: raise ValueError("b не может быть 0.")
            add = a + b; sub = a - b; mul = a * b; div_floor = a // b
            modv = a % b; modexp_v = mod_exp(a, n, m)
            try:
                div_float = a / b
                if abs(div_float) > 1e300: div_str = "слишком большое"
                else:
                    div_str = f"{div_float:.20g}"
                    if '.' not in div_str and 'e' not in div_str:
                        div_str += ".0"
            except Exception:
                div_str = "ошибка"
            report = f"""Операции:
a = {a}
b = {b}
n = {n}
m = {m}

a + b = {add}
a - b = {sub}
a * b = {mul}
a // b = {div_floor}
a / b = {div_str}
a mod b = {modv}
a^{n} mod {m} = {modexp_v}
"""
            self.results.setPlainText(report)
        except Exception as e:
            QMessageBox.critical(self, "❌ Вычисления", str(e))

    def export(self):
        text = self.results.toPlainText().strip()
        if not text:
            QMessageBox.warning(self, "⚠️ Пусто", "Нет данных.")
            return
        path, _ = QFileDialog.getSaveFileName(self, "Сохранить", "", "Text Files (*.txt)")
        if path:
            try:
                with open(path, 'w', encoding='utf-8') as f:
                    f.write(text)
                QMessageBox.information(self, "✅ Сохранено", f"Файл:\n{path}")
            except Exception as e:
                QMessageBox.critical(self, "❌ Ошибка", str(e))

# ===========================
# RSA утилиты
# ===========================
def extended_gcd(a, b):
    if a == 0: return b, 0, 1
    g, x1, y1 = extended_gcd(b % a, a)
    return g, y1 - (b // a)*x1, x1

def mod_inverse(a, m):
    g, x, _ = extended_gcd(a, m)
    if g != 1:
        raise ValueError("Обратный элемент не существует.")
    return x % m

LETTER_TO_NUM = {
    'А':'10','Б':'11','В':'12','Г':'13','Д':'14','Е':'15','Ж':'16','З':'17',
    'И':'18','Й':'19','К':'20','Л':'21','М':'22','Н':'23','О':'24','П':'25',
    'Р':'26','С':'27','Т':'28','У':'29','Ф':'30','Х':'31','Ц':'32','Ч':'33',
    'Ш':'34','Щ':'35','Ъ':'36','Ы':'37','Ь':'38','Э':'39','Ю':'40','Я':'41',' ':'99'
}
NUM_TO_LETTER = {v:k for k,v in LETTER_TO_NUM.items()}

def text_to_digits(text):
    """
    Кодирует произвольный текст в цифровую строку через UTF‑8.
    Каждый байт представляется тремя цифрами 000–255.
    """
    data = text.encode('utf-8')
    return ''.join(f"{b:03d}" for b in data)

def digits_to_text(digits):
    """
    Обратное преобразование цифровой строки в текст UTF‑8.
    Ожидает, что длина строки кратна 3, каждые 3 цифры — один байт (0–255).
    """
    if len(digits) % 3 != 0:
        raise ValueError("Некорректная длина цифровой строки (не кратна 3).")
    bytes_arr = bytearray()
    for i in range(0, len(digits), 3):
        chunk = digits[i:i+3]
        try:
            val = int(chunk)
        except ValueError:
            raise ValueError(f"Некорректный байт '{chunk}' в цифровой строке.")
        if not (0 <= val <= 255):
            raise ValueError(f"Байт вне диапазона 0–255: {val}.")
        bytes_arr.append(val)
    return bytes_arr.decode('utf-8', errors='replace')

def split_into_blocks(num_str, N):
    if not num_str: return []
    blocks = []; i = 0
    while i < len(num_str):
        max_len = len(str(N - 1))
        found = False
        for length in range(min(max_len, len(num_str)-i), 0, -1):
            part = num_str[i:i+length]
            val = int(part)
            if val < N:
                blocks.append(val)
                i += length
                found = True
                break
        if not found:
            raise ValueError(f"Остаток '{num_str[i:]}' ≥ N={N}")
    return blocks

def parse_numbers(text):
    """
    Принимает строку формата:
      [1,2,3]  или  1,2,3  или  1 2 3  или  1;2;3
    Возвращает список int.
    """
    if not text.strip():
        return []
    cleaned = text.strip()
    for ch in '[]{}()':
        cleaned = cleaned.replace(ch, ' ')
    cleaned = cleaned.replace(';', ' ').replace(',', ' ')
    parts = [p for p in cleaned.split() if p]
    nums = []
    for p in parts:
        if not p.isdigit():
            raise ValueError(f"Некорректный элемент списка: '{p}'")
        nums.append(int(p))
    return nums

# ===========================
# Вкладка 3: RSA (Упрощённая версия)
# ===========================
class RSATab(QWidget):
    def __init__(self):
        super().__init__()
        layout = QVBoxLayout(self)
        
        # ========== ШАГ 1: Генерация простых чисел ==========
        step1_group = QGroupBox("Шаг 1: Генерация простых чисел p и q")
        step1_layout = QVBoxLayout()
        
        # Режим генерации
        mode_row = QHBoxLayout()
        mode_row.addWidget(QLabel("Режим:"))
        self.gen_mode_combo = QComboBox()
        self.gen_mode_combo.addItems([
            "Автоматическая генерация",
            "Ввод вручную"
        ])
        self.gen_mode_combo.currentIndexChanged.connect(self.on_gen_mode_changed)
        mode_row.addWidget(self.gen_mode_combo)
        mode_row.addStretch()
        step1_layout.addLayout(mode_row)
        
        # Параметры автогенерации
        self.auto_gen_widget = QWidget()
        auto_gen_layout = QVBoxLayout(self.auto_gen_widget)
        
        bits_row = QHBoxLayout()
        bits_row.addWidget(QLabel("Битность:"))
        self.bits_spin = QSpinBox()
        self.bits_spin.setRange(RSA_MIN_BITS, RSA_MAX_BITS)
        self.bits_spin.setValue(16)
        bits_row.addWidget(self.bits_spin)
        bits_row.addWidget(QLabel("бит (рекомендуется: 16-64 для быстрой работы)"))
        bits_row.addStretch()
        auto_gen_layout.addLayout(bits_row)
        
        gen_btn_row = QHBoxLayout()
        self.btn_generate_pq = QPushButton("🎲 Сгенерировать p и q")
        self.btn_generate_pq.clicked.connect(self.generate_pq)
        gen_btn_row.addWidget(self.btn_generate_pq)
        gen_btn_row.addStretch()
        auto_gen_layout.addLayout(gen_btn_row)
        
        step1_layout.addWidget(self.auto_gen_widget)
        
        # Поля для p и q
        pq_row = QHBoxLayout()
        pq_row.addWidget(QLabel("p:"))
        self.p_edit = QLineEdit()
        self.p_edit.setPlaceholderText("Введите или сгенерируйте p")
        pq_row.addWidget(self.p_edit)
        pq_row.addWidget(QLabel("q:"))
        self.q_edit = QLineEdit()
        self.q_edit.setPlaceholderText("Введите или сгенерируйте q")
        pq_row.addWidget(self.q_edit)
        step1_layout.addLayout(pq_row)
        
        step1_group.setLayout(step1_layout)
        layout.addWidget(step1_group)
        
        # ========== ШАГ 2: Вычисление ключей ==========
        step2_group = QGroupBox("Шаг 2: Вычисление ключей RSA")
        step2_layout = QVBoxLayout()
        
        # Режим ключей
        key_mode_row = QHBoxLayout()
        key_mode_row.addWidget(QLabel("Режим:"))
        self.key_mode_combo = QComboBox()
        self.key_mode_combo.addItems([
            "Вычислить из p и q",
            "Ввести ключи вручную"
        ])
        self.key_mode_combo.currentIndexChanged.connect(self.on_key_mode_changed)
        key_mode_row.addWidget(self.key_mode_combo)
        key_mode_row.addStretch()
        step2_layout.addLayout(key_mode_row)
        
        # Режим вычисления из p и q
        self.calc_mode_widget = QWidget()
        calc_mode_layout = QVBoxLayout(self.calc_mode_widget)
        
        e_row = QHBoxLayout()
        e_row.addWidget(QLabel("Открытая экспонента e:"))
        self.e_edit = QLineEdit("65537")
        e_row.addWidget(self.e_edit)
        self.btn_calc_keys = QPushButton("🔑 Вычислить ключи")
        self.btn_calc_keys.clicked.connect(self.calculate_keys)
        e_row.addWidget(self.btn_calc_keys)
        e_row.addStretch()
        calc_mode_layout.addLayout(e_row)
        
        step2_layout.addWidget(self.calc_mode_widget)
        
        # Режим ручного ввода ключей
        self.manual_mode_widget = QWidget()
        manual_mode_layout = QVBoxLayout(self.manual_mode_widget)
        
        manual_row1 = QHBoxLayout()
        manual_row1.addWidget(QLabel("N:"))
        self.N_edit = QLineEdit()
        self.N_edit.setPlaceholderText("Введите N (модуль)")
        manual_row1.addWidget(self.N_edit)
        manual_row1.addWidget(QLabel("e:"))
        self.e_manual_edit = QLineEdit("65537")
        self.e_manual_edit.setPlaceholderText("Введите e")
        manual_row1.addWidget(self.e_manual_edit)
        manual_mode_layout.addLayout(manual_row1)
        
        manual_row2 = QHBoxLayout()
        manual_row2.addWidget(QLabel("d:"))
        self.d_edit = QLineEdit()
        self.d_edit.setPlaceholderText("Введите d (секретная экспонента)")
        manual_row2.addWidget(self.d_edit)
        self.btn_set_manual = QPushButton("✅ Установить ключи")
        self.btn_set_manual.clicked.connect(self.set_manual_keys)
        manual_row2.addWidget(self.btn_set_manual)
        manual_row2.addStretch()
        manual_mode_layout.addLayout(manual_row2)
        
        self.manual_mode_widget.setVisible(False)
        step2_layout.addWidget(self.manual_mode_widget)
        
        # Отображение ключей
        keys_display = QHBoxLayout()
        self.keys_label = QLabel("Ключи: не вычислены")
        self.keys_label.setWordWrap(True)
        keys_display.addWidget(self.keys_label)
        step2_layout.addLayout(keys_display)
        
        key_buttons = QHBoxLayout()
        self.btn_save_keys = QPushButton("💾 Сохранить ключи")
        self.btn_save_keys.clicked.connect(self.save_keys)
        self.btn_load_keys = QPushButton("📥 Загрузить ключи")
        self.btn_load_keys.clicked.connect(self.load_keys)
        key_buttons.addWidget(self.btn_save_keys)
        key_buttons.addWidget(self.btn_load_keys)
        key_buttons.addStretch()
        step2_layout.addLayout(key_buttons)
        
        step2_group.setLayout(step2_layout)
        layout.addWidget(step2_group)
        
        # ========== ШАГ 3: Шифрование/Дешифрование ==========
        step3_group = QGroupBox("Шаг 3: Операции шифрования и дешифрования")
        step3_layout = QVBoxLayout()
        
        # Панель ввода/вывода
        splitter = QSplitter(Qt.Horizontal)
        
        # Левая панель - Ввод
        input_group = QGroupBox("Ввод")
        input_layout = QVBoxLayout()
        self.input_text = QTextEdit()
        self.input_text.setPlaceholderText(
            "Введите текст для шифрования или зашифрованные блоки для расшифрования.\n\n"
            "Примеры:\n"
            "- Для шифрования: Привет мир\n"
            "- Для расшифрования: 12345,67890,11111"
        )
        input_layout.addWidget(self.input_text)
        
        input_buttons = QHBoxLayout()
        self.btn_load_file = QPushButton("📂 Загрузить файл")
        self.btn_load_file.clicked.connect(self.load_file)
        self.btn_clear_input = QPushButton("🗑 Очистить")
        self.btn_clear_input.clicked.connect(self.input_text.clear)
        input_buttons.addWidget(self.btn_load_file)
        input_buttons.addWidget(self.btn_clear_input)
        input_buttons.addStretch()
        input_layout.addLayout(input_buttons)
        
        input_group.setLayout(input_layout)
        splitter.addWidget(input_group)
        
        # Правая панель - Вывод
        output_group = QGroupBox("Результат")
        output_layout = QVBoxLayout()
        self.output_text = QTextEdit()
        self.output_text.setReadOnly(True)
        self.output_text.setPlaceholderText("Результаты операций будут отображаться здесь...")
        output_layout.addWidget(self.output_text)
        
        output_buttons = QHBoxLayout()
        self.btn_save_file = QPushButton("💾 Сохранить файл")
        self.btn_save_file.clicked.connect(self.save_file)
        self.btn_copy = QPushButton("📋 Копировать")
        self.btn_copy.clicked.connect(self.copy_output)
        self.btn_clear_output = QPushButton("🗑 Очистить")
        self.btn_clear_output.clicked.connect(self.output_text.clear)
        output_buttons.addWidget(self.btn_save_file)
        output_buttons.addWidget(self.btn_copy)
        output_buttons.addWidget(self.btn_clear_output)
        output_buttons.addStretch()
        output_layout.addLayout(output_buttons)
        
        output_group.setLayout(output_layout)
        splitter.addWidget(output_group)
        
        step3_layout.addWidget(splitter)
        
        # Лог операций
        log_group = QGroupBox("Лог операций")
        log_layout = QVBoxLayout()
        self.log_text = QTextEdit()
        self.log_text.setReadOnly(True)
        self.log_text.setPlaceholderText("Детали операций будут отображаться здесь...")
        self.log_text.setMaximumHeight(150)
        log_layout.addWidget(self.log_text)
        log_group.setLayout(log_layout)
        step3_layout.addWidget(log_group)
        
        # Кнопки операций
        ops_row = QHBoxLayout()
        self.btn_prepare = QPushButton("🧾 Подготовить блоки")
        self.btn_prepare.clicked.connect(self.prepare_blocks)
        self.btn_encrypt = QPushButton("🔒 Зашифровать")
        self.btn_encrypt.clicked.connect(self.encrypt)
        self.btn_decrypt = QPushButton("🔓 Расшифровать")
        self.btn_decrypt.clicked.connect(self.decrypt)
        ops_row.addWidget(self.btn_prepare)
        ops_row.addWidget(self.btn_encrypt)
        ops_row.addWidget(self.btn_decrypt)
        ops_row.addStretch()
        step3_layout.addLayout(ops_row)
        
        step3_group.setLayout(step3_layout)
        layout.addWidget(step3_group)
        
        # Инициализация переменных
        self.N = None
        self.e_val = None
        self.d = None
        self.phi = None
        self.blocks = []
        self.cipher_blocks = []
    
    # ========== Методы RSA ==========
    
    def on_gen_mode_changed(self, index):
        """Переключение режима генерации"""
        if index == 0:  # Автоматическая генерация
            self.auto_gen_widget.setVisible(True)
            self.btn_generate_pq.setEnabled(True)
        else:  # Ввод вручную
            self.auto_gen_widget.setVisible(False)
            self.btn_generate_pq.setEnabled(False)
    
    def on_key_mode_changed(self, index):
        """Переключение режима ключей"""
        if index == 0:  # Вычислить из p и q
            self.calc_mode_widget.setVisible(True)
            self.manual_mode_widget.setVisible(False)
        else:  # Ввести ключи вручную
            self.calc_mode_widget.setVisible(False)
            self.manual_mode_widget.setVisible(True)
    
    def set_manual_keys(self):
        """Установка ключей вручную"""
        try:
            N_text = self.N_edit.text().strip()
            e_text = self.e_manual_edit.text().strip()
            d_text = self.d_edit.text().strip()
            
            if not N_text or not e_text or not d_text:
                raise ValueError("Введите все параметры: N, e, d")
            
            self.N = int(N_text)
            self.e_val = int(e_text)
            self.d = int(d_text)
            
            if self.N < 2:
                raise ValueError("N должно быть >= 2")
            if self.e_val <= 1:
                raise ValueError("e должно быть > 1")
            if self.d <= 1:
                raise ValueError("d должно быть > 1")
            
            self.phi = None  # Неизвестно при ручном вводе
            
            # Обновляем отображение
            self.keys_label.setText(
                f"Открытый ключ: (N={self.N}, e={self.e_val})\n"
                f"Секретный ключ: d={self.d}\n"
                f"φ(N) = ? (неизвестно при ручном вводе)"
            )
            
            # Обновляем поле e в режиме расчета
            self.e_edit.setText(str(self.e_val))
            
            self.log_text.append(
                f"[Ручной ввод ключей]\n"
                f"N = {self.N}\n"
                f"e = {self.e_val}\n"
                f"d = {self.d}\n"
            )
            
            QMessageBox.information(
                self, "✅ Ключи установлены",
                f"Ключи успешно установлены вручную!\n\n"
                f"N = {self.N}\n"
                f"e = {self.e_val}\n"
                f"d = {self.d}"
            )
        except Exception as e:
            QMessageBox.critical(self, "❌ Ошибка", str(e))
    
    def generate_pq(self):
        """Генерация простых чисел p и q"""
        try:
            bits = self.bits_spin.value()
            
            # Выбираем оптимальный метод генерации
            if bits <= 20:
                method = "sieve"
            elif bits <= 24:
                method = "genpr"
            elif bits <= 32:
                method = "trial"
            else:
                method = "miller-rabin"
            
            # Генерируем p
            p = generate_large_prime(bits, method)
            
            # Генерируем q (должно быть отличным от p)
            q = generate_large_prime(bits, method)
            attempts = 0
            while q == p and attempts < RSA_MAX_GENERATION_ATTEMPTS:
                q = generate_large_prime(bits, method)
                attempts += 1
            
            if q == p:
                raise ValueError("Не удалось сгенерировать различные простые числа.")
            
            self.p_edit.setText(str(p))
            self.q_edit.setText(str(q))
            
            self.log_text.append(
                f"[Генерация простых чисел]\n"
                f"Битность: {bits}\n"
                f"Метод: {method}\n"
                f"p = {p}\n"
                f"q = {q}\n"
                f"p × q = {p * q}\n"
            )
            
            QMessageBox.information(
                self, "✅ Успех",
                f"Простые числа сгенерированы!\n\n"
                f"p = {p}\n"
                f"q = {q}\n"
                f"Метод: {method}\n\n"
                f"Теперь нажмите 'Вычислить ключи'."
            )
        except Exception as e:
            QMessageBox.critical(self, "❌ Ошибка генерации", str(e))
    
    def calculate_keys(self):
        """Вычисление ключей RSA из p и q"""
        try:
            # Получаем p и q
            p_text = self.p_edit.text().strip()
            q_text = self.q_edit.text().strip()
            
            if not p_text or not q_text:
                raise ValueError("Введите p и q (или сгенерируйте их).")
            
            p = int(p_text)
            q = int(q_text)
            
            if p < 2 or q < 2:
                raise ValueError("p и q должны быть >= 2.")
            
            if p == q:
                raise ValueError("p и q должны быть различными.")
            
            # Вычисляем N и φ(N)
            self.N = p * q
            self.phi = (p - 1) * (q - 1)
            
            # Получаем e
            e_text = self.e_edit.text().strip()
            if not e_text:
                e = 65537
            else:
                e = int(e_text)
            
            # Проверяем корректность e
            if e <= 1 or e >= self.phi:
                raise ValueError(f"e должно быть в диапазоне (1, {self.phi}).")
            
            # Проверяем взаимную простоту e и φ(N)
            g, _, _ = extended_gcd(e, self.phi)
            if g != 1:
                # Пытаемся найти подходящее e
                for candidate in RSA_COMMON_E_VALUES:
                    if 1 < candidate < self.phi:
                        g2, _, _ = extended_gcd(candidate, self.phi)
                        if g2 == 1:
                            e = candidate
                            self.e_edit.setText(str(e))
                            QMessageBox.information(
                                self, "ℹ️ Автоматический выбор e",
                                f"Введённое значение e не подходит.\n"
                                f"Автоматически выбрано e = {e}."
                            )
                            break
                else:
                    raise ValueError(f"Не удалось найти подходящее e для данных p и q.")
            
            self.e_val = e
            
            # Вычисляем d (секретную экспоненту)
            self.d = mod_inverse(e, self.phi)
            
            # Обновляем отображение
            self.keys_label.setText(
                f"Открытый ключ: (N={self.N}, e={e})\n"
                f"Секретный ключ: d={self.d}\n"
                f"φ(N)={self.phi}"
            )
            
            self.log_text.append(
                f"[Вычисление ключей]\n"
                f"p = {p}\n"
                f"q = {q}\n"
                f"N = p × q = {self.N}\n"
                f"φ(N) = (p-1) × (q-1) = {self.phi}\n"
                f"e = {e}\n"
                f"d = e⁻¹ mod φ(N) = {self.d}\n"
            )
            
            QMessageBox.information(
                self, "✅ Ключи готовы",
                f"RSA ключи успешно вычислены!\n\n"
                f"N = {self.N}\n"
                f"e = {e}\n"
                f"d = {self.d}\n\n"
                f"Теперь можно шифровать и расшифровывать."
            )
        except Exception as e:
            QMessageBox.critical(self, "❌ Ошибка вычисления", str(e))
    
    def prepare_blocks(self):
        """Подготовка блоков из текста"""
        try:
            if self.N is None:
                raise ValueError("Сначала вычислите ключи (N должно быть определено).")
            
            text = self.input_text.toPlainText().strip()
            if not text:
                raise ValueError("Введите текст для подготовки блоков.")
            
            # Преобразуем текст в цифры
            digits = text_to_digits(text)
            
            # Разбиваем на блоки
            self.blocks = split_into_blocks(digits, self.N)
            
            # Формируем результат
            blocks_str = ','.join(map(str, self.blocks))
            
            # Выводим в результат
            self.output_text.setPlainText(blocks_str)
            
            self.log_text.append(
                f"[Подготовка блоков]\n"
                f"Текст: {text[:RSA_MSG_TRUNCATE_SHORT]}{'...' if len(text) > RSA_MSG_TRUNCATE_SHORT else ''}\n"
                f"Блоков: {len(self.blocks)}\n"
                f"N = {self.N}\n"
            )
            
            QMessageBox.information(
                self, "✅ Подготовка выполнена",
                f"Подготовлено {len(self.blocks)} блоков.\n\n"
                f"Блоки: {blocks_str[:RSA_MSG_TRUNCATE_LONG]}{'...' if len(blocks_str) > RSA_MSG_TRUNCATE_LONG else ''}"
            )
        except Exception as e:
            QMessageBox.critical(self, "❌ Ошибка подготовки", str(e))
    
    def encrypt(self):
        """Шифрование текста"""
        try:
            if self.N is None or self.e_val is None:
                raise ValueError("Сначала вычислите ключи RSA.")
            
            text = self.input_text.toPlainText().strip()
            if not text:
                raise ValueError("Введите текст для шифрования.")
            
            # Преобразуем текст в цифры (UTF-8)
            digits = text_to_digits(text)
            
            # Разбиваем на блоки
            blocks = split_into_blocks(digits, self.N)
            self.blocks = blocks
            
            # Шифруем каждый блок
            self.cipher_blocks = [mod_exp(m, self.e_val, self.N) for m in blocks]
            
            # Формируем результат
            cipher_str = ','.join(map(str, self.cipher_blocks))
            
            # Выводим результат
            self.output_text.setPlainText(cipher_str)
            
            self.log_text.append(
                f"[Шифрование]\n"
                f"Текст: {text[:RSA_MSG_TRUNCATE_SHORT]}{'...' if len(text) > RSA_MSG_TRUNCATE_SHORT else ''}\n"
                f"Блоков M_i: {len(blocks)}\n"
                f"Блоков C_i: {len(self.cipher_blocks)}\n"
                f"Параметры: N={self.N}, e={self.e_val}\n"
            )
            
            QMessageBox.information(
                self, "✅ Шифрование выполнено",
                f"Текст зашифрован!\n\n"
                f"Исходный текст: {text[:RSA_MSG_TRUNCATE_SHORT]}{'...' if len(text) > RSA_MSG_TRUNCATE_SHORT else ''}\n"
                f"Количество блоков: {len(self.cipher_blocks)}\n\n"
                f"Зашифрованные блоки скопированы в поле 'Результат'."
            )
        except Exception as e:
            QMessageBox.critical(self, "❌ Ошибка шифрования", str(e))
    
    def decrypt(self):
        """Расшифрование блоков"""
        try:
            if self.N is None or self.d is None:
                raise ValueError("Сначала вычислите ключи RSA.")
            
            text = self.input_text.toPlainText().strip()
            if not text:
                raise ValueError("Введите зашифрованные блоки для расшифрования.")
            
            # Парсим блоки
            cipher_blocks = parse_numbers(text)
            if not cipher_blocks:
                raise ValueError("Не удалось распарсить зашифрованные блоки.\nВведите числа через запятую.")
            
            self.cipher_blocks = cipher_blocks
            
            # Расшифровываем каждый блок
            decrypted_blocks = [mod_exp(c, self.d, self.N) for c in cipher_blocks]
            
            # Собираем цифровую строку
            digits = ''.join(str(m) for m in decrypted_blocks)
            
            # Преобразуем обратно в текст
            try:
                decrypted_text = digits_to_text(digits)
            except Exception as e:
                raise ValueError(f"Ошибка декодирования текста: {e}\n\n"
                               f"Возможно, блоки зашифрованы другим ключом.")
            
            # Выводим результат
            self.output_text.setPlainText(decrypted_text)
            
            self.log_text.append(
                f"[Расшифрование]\n"
                f"Блоков C_i: {len(cipher_blocks)}\n"
                f"Блоков M_i: {len(decrypted_blocks)}\n"
                f"Текст: {decrypted_text[:RSA_MSG_TRUNCATE_SHORT]}{'...' if len(decrypted_text) > RSA_MSG_TRUNCATE_SHORT else ''}\n"
                f"Параметры: N={self.N}, d={self.d}\n"
            )
            
            QMessageBox.information(
                self, "✅ Расшифрование выполнено",
                f"Блоки расшифрованы!\n\n"
                f"Расшифрованный текст:\n{decrypted_text[:RSA_MSG_TRUNCATE_LONG]}{'...' if len(decrypted_text) > RSA_MSG_TRUNCATE_LONG else ''}"
            )
        except Exception as e:
            QMessageBox.critical(self, "❌ Ошибка расшифрования", str(e))
    
    def save_keys(self):
        """Сохранение ключей в файл"""
        if self.N is None or self.e_val is None or self.d is None:
            QMessageBox.warning(self, "⚠️ Нет ключей", "Сначала вычислите ключи RSA.")
            return
        
        path, _ = QFileDialog.getSaveFileName(
            self, "Сохранить ключи", "", "Text Files (*.txt);;All Files (*)"
        )
        if path:
            try:
                content = f"""RSA Ключи
==========

Открытый ключ:
N={self.N}
e={self.e_val}

Секретный ключ:
d={self.d}

Дополнительная информация:
phi={self.phi if self.phi else 'неизвестно'}
p={self.p_edit.text() if self.p_edit.text() else 'неизвестно'}
q={self.q_edit.text() if self.q_edit.text() else 'неизвестно'}
"""
                with open(path, 'w', encoding='utf-8') as f:
                    f.write(content)
                QMessageBox.information(self, "✅ Сохранено", f"Ключи сохранены в:\n{path}")
            except Exception as e:
                QMessageBox.critical(self, "❌ Ошибка", f"Не удалось сохранить:\n{e}")
    
    def load_keys(self):
        """Загрузка ключей из файла"""
        path, _ = QFileDialog.getOpenFileName(
            self, "Загрузить ключи", "", "Text Files (*.txt);;All Files (*)"
        )
        if path:
            try:
                with open(path, 'r', encoding='utf-8') as f:
                    content = f.read()
                
                # Парсим файл
                N_val = None
                e_val = None
                d_val = None
                p_val = None
                q_val = None
                phi_val = None
                
                for line in content.split('\n'):
                    line = line.strip()
                    if '=' in line and not line.startswith('#'):
                        key, value = line.split('=', 1)
                        key = key.strip().lower()
                        value = value.strip()
                        
                        if value and value != 'неизвестно':
                            try:
                                if key == 'n':
                                    N_val = int(value)
                                elif key == 'e':
                                    e_val = int(value)
                                elif key == 'd':
                                    d_val = int(value)
                                elif key == 'p':
                                    p_val = int(value)
                                elif key == 'q':
                                    q_val = int(value)
                                elif key == 'phi':
                                    phi_val = int(value)
                            except ValueError:
                                pass
                
                if N_val is None or e_val is None or d_val is None:
                    raise ValueError("Файл не содержит необходимых ключей (N, e, d).")
                
                # Устанавливаем ключи
                self.N = N_val
                self.e_val = e_val
                self.d = d_val
                self.phi = phi_val
                
                # Обновляем UI
                self.e_edit.setText(str(e_val))
                if p_val:
                    self.p_edit.setText(str(p_val))
                if q_val:
                    self.q_edit.setText(str(q_val))
                
                self.keys_label.setText(
                    f"Открытый ключ: (N={self.N}, e={e_val})\n"
                    f"Секретный ключ: d={self.d}\n"
                    f"φ(N)={phi_val if phi_val else '?'}"
                )
                
                QMessageBox.information(
                    self, "✅ Загружено",
                    f"Ключи успешно загружены из:\n{path}\n\n"
                    f"N = {N_val}\n"
                    f"e = {e_val}\n"
                    f"d = {d_val}"
                )
            except Exception as e:
                QMessageBox.critical(self, "❌ Ошибка", f"Не удалось загрузить:\n{e}")
    
    def load_file(self):
        """Загрузка текста из файла"""
        path, _ = QFileDialog.getOpenFileName(
            self, "Загрузить файл", "", "Text Files (*.txt);;All Files (*)"
        )
        if path:
            try:
                with open(path, 'r', encoding='utf-8') as f:
                    content = f.read()
                self.input_text.setPlainText(content)
                QMessageBox.information(self, "✅ Загружено", f"Файл загружен:\n{path}")
            except Exception as e:
                QMessageBox.critical(self, "❌ Ошибка", f"Не удалось загрузить:\n{e}")
    
    def save_file(self):
        """Сохранение результата в файл"""
        content = self.output_text.toPlainText()
        if not content:
            QMessageBox.warning(self, "⚠️ Нет данных", "Результат пуст.")
            return
        
        path, _ = QFileDialog.getSaveFileName(
            self, "Сохранить результат", "", "Text Files (*.txt);;All Files (*)"
        )
        if path:
            try:
                with open(path, 'w', encoding='utf-8') as f:
                    f.write(content)
                QMessageBox.information(self, "✅ Сохранено", f"Результат сохранён в:\n{path}")
            except Exception as e:
                QMessageBox.critical(self, "❌ Ошибка", f"Не удалось сохранить:\n{e}")
    
    def copy_output(self):
        """Копирование результата в буфер обмена"""
        content = self.output_text.toPlainText()
        if not content:
            QMessageBox.warning(self, "⚠️ Нет данных", "Результат пуст.")
            return
        QApplication.clipboard().setText(content)
        QMessageBox.information(self, "📋 Скопировано", "Результат скопирован в буфер обмена.")

class CryptoSuite(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Криптографический практикум (ПЗ-9, ПЗ-10, ПЗ-11)")
        self.resize(1200, 800)
        self.current_theme = "light"
        central = QWidget()
        self.setCentralWidget(central)
        layout = QVBoxLayout(central)
        tabs = QTabWidget()
        tabs.addTab(GammaTab(), "🔒 ПЗ-9: Гаммирование")
        tabs.addTab(ModArithmeticTab(), "🧮 ПЗ-10: Модулярная арифметика")
        tabs.addTab(RSATab(), "🔐 ПЗ-11: RSA")
        layout.addWidget(tabs)
        self.apply_style_light()
        self.create_menu()

    def create_menu(self):
        menubar = QMenuBar(self)
        view_menu = menubar.addMenu("Вид")
        act_light = QAction("Светлая тема", self)
        act_dark = QAction("Тёмная тема", self)
        act_light.triggered.connect(self.apply_style_light)
        act_dark.triggered.connect(self.apply_style_dark)
        view_menu.addAction(act_light)
        view_menu.addAction(act_dark)
        self.setMenuBar(menubar)

    def apply_common_styles(self):
        font = QFont("Segoe UI", 10)
        self.setFont(font)
        self.setStyleSheet(self.styleSheet() + """
            QGroupBox {
                border: 1px solid #b0b0b0;
                border-radius: 8px;
                margin-top: 12px;
                padding: 8px;
                font-weight: bold;
            }
            QGroupBox::title {
                subcontrol-origin: margin;
                subcontrol-position: top left;
                padding: 0 6px;
            }
            QPushButton {
                padding: 6px 12px;
                border-radius: 6px;
                font-weight: 500;
            }
            QLineEdit, QTextEdit, QSpinBox, QComboBox {
                border: 1px solid #b8b8b8;
                border-radius: 6px;
                padding: 4px;
            }
            QTabBar::tab {
                padding: 6px 14px;
                margin: 4px;
                border-radius: 6px;
                font-weight: 500;
            }
            QTabWidget::pane { border: 1px solid #b0b0b0; }
            QSplitter::handle { background: #d2d2d2; }
        """)

    def apply_style_light(self):
        self.current_theme = "light"
        palette = QPalette()
        palette.setColor(QPalette.Window, QColor("#F7F9FA"))
        palette.setColor(QPalette.WindowText, QColor("#202124"))
        palette.setColor(QPalette.Base, QColor("#FFFFFF"))
        palette.setColor(QPalette.AlternateBase, QColor("#F0F3F5"))
        palette.setColor(QPalette.Text, QColor("#202124"))
        palette.setColor(QPalette.Button, QColor("#E8EBF0"))
        palette.setColor(QPalette.ButtonText, QColor("#202124"))
        palette.setColor(QPalette.Highlight, QColor("#4A73F3"))
        palette.setColor(QPalette.HighlightedText, QColor("#FFFFFF"))
        self.setPalette(palette)
        self.setStyleSheet("""
            QPushButton {
                background-color: #4A73F3;
                color: #ffffff;
            }
            QPushButton:hover { background-color: #335ee0; }
            QPushButton:pressed { background-color: #284bb9; }
            QTabBar::tab {
                background: #E1E5EC;
                color: #1F2225;
            }
            QTabBar::tab:selected {
                background: #4A73F3;
                color: #fff;
            }
            QLineEdit, QTextEdit, QSpinBox, QComboBox {
                background: #FFFFFF;
                color: #202124;
            }
        """)
        self.apply_common_styles()

    def apply_style_dark(self):
        self.current_theme = "dark"
        palette = QPalette()
        palette.setColor(QPalette.Window, QColor("#1E2127"))
        palette.setColor(QPalette.WindowText, QColor("#E6E6E6"))
        palette.setColor(QPalette.Base, QColor("#2B2F36"))
        palette.setColor(QPalette.AlternateBase, QColor("#323841"))
        palette.setColor(QPalette.Text, QColor("#E0E0E0"))
        palette.setColor(QPalette.Button, QColor("#3B414B"))
        palette.setColor(QPalette.ButtonText, QColor("#F5F5F5"))
        palette.setColor(QPalette.Highlight, QColor("#5865F2"))
        palette.setColor(QPalette.HighlightedText, QColor("#000000"))
        self.setPalette(palette)
        self.setStyleSheet("""
            QPushButton {
                background-color: #5865F2;
                color: #ffffff;
            }
            QPushButton:hover { background-color: #4752c4; }
            QPushButton:pressed { background-color: #3942a1; }
            QTabBar::tab {
                background: #3b3f46;
                color: #ddd;
            }
            QTabBar::tab:selected {
                background: #5865F2;
                color: #fff;
            }
            QLineEdit, QTextEdit, QSpinBox, QComboBox {
                background: #2e3138;
                color: #ddd;
                border: 1px solid #555;
            }
        """)
        self.apply_common_styles()

# ===========================
# Запуск
# ===========================
if __name__ == "__main__":
    app = QApplication(sys.argv)
    window = CryptoSuite()
    window.show()
    sys.exit(app.exec())