import sys,secrets,math,json,base64
from PySide6.QtWidgets import QApplication,QMainWindow,QWidget,QVBoxLayout,QHBoxLayout,QTabWidget,QPushButton,QTextEdit,QLabel,QLineEdit,QFileDialog,QComboBox,QGroupBox,QMessageBox,QSplitter,QSpinBox,QMenuBar
from PySide6.QtCore import Qt
from PySide6.QtGui import QFont,QPalette,QColor,QAction
from cryptography.hazmat.primitives.asymmetric import rsa as crypto_rsa,padding as crypto_padding
from cryptography.hazmat.primitives import hashes,serialization
METHOD_MAX_BITS={"miller-rabin":1024,"trial":32,"sieve":20,"genpr":24}
class LCG:
    def __init__(self,seed,a=1664525,b=1013904223,m=2**32):
        if b%2==0: raise ValueError("LCG: b должно быть нечётным (по Кнуту)")
        if a%4!=1: raise ValueError("LCG: a ≡ 1 (mod 4)")
        self.state=seed%m;self.a=a;self.b=b;self.m=m
    def next(self):
        self.state=(self.a*self.state+self.b)%self.m
        return self.state
class Multiplicative:
    def __init__(self,seed,a=16807,m=2**31-1):
        if seed==0: raise ValueError("Мультипликативный генератор: seed ≠ 0")
        self.state=seed%m;self.a=a;self.m=m
    def next(self):
        self.state=(self.a*self.state)%self.m
        return self.state
class Additive:
    def __init__(self,seed1,seed2=None,m=2**32):
        self.x=seed1%m;self.y=(seed2 or (seed1*1103515245+12345))%m;self.m=m
    def next(self):
        z=(self.x+self.y)%self.m;self.x,self.y=self.y,z;return z
def apply_gamma(data_bytes,gen):
    result=bytearray();block_size=8
    for i in range(0,len(data_bytes),block_size):
        block=data_bytes[i:i+block_size]
        gamma=bytearray(gen.next()&0xFF for _ in range(len(block)))
        encrypted=bytearray(b^g for b,g in zip(block,gamma))
        result.extend(encrypted)
    return bytes(result)
_SMALL_PRIMES=[2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
for n in range(101,1000,2):
    if all(n%p for p in _SMALL_PRIMES if p*p<=n): _SMALL_PRIMES.append(n)
def is_prime_deterministic(n):
    if n<2: return False
    for p in _SMALL_PRIMES:
        if n%p==0: return n==p
    d=n-1;s=0
    while d%2==0: d//=2;s+=1
    for a in [2,325,9375,28178,450775,9780504,1795265022]:
        if a%n==0: continue
        x=pow(a,d,n)
        if x==1 or x==n-1: continue
        for _ in range(s-1):
            x=(x*x)%n
            if x==n-1: break
        else: return False
    return True
def is_prime_miller_rabin(n,k=10):
    if n<2: return False
    for p in _SMALL_PRIMES[:15]:
        if n%p==0: return n==p
    d=n-1;s=0
    while d%2==0: d//=2;s+=1
    for _ in range(k):
        a=secrets.randbelow(n-3)+2
        x=pow(a,d,n)
        if x==1 or x==n-1: continue
        for __ in range(s-1):
            x=(x*x)%n
            if x==n-1: break
        else: return False
    return True
def genpr_algorithm(m,k):
    if m%2==0: m+=1
    A=[1]*k;d=3
    while d*d<=m+2*k-2:
        r=m%d
        if r==0: j=0
        else:
            inv2=pow(2,-1,d);j=((-r)*inv2)%d
        jj=j
        while jj<k:
            if m+2*jj!=d: A[jj]=0
            jj+=d
        d=d+4 if d%6==1 else d+2
    primes=[]
    for i in range(k):
        if A[i]:
            cand=m+2*i
            if cand>=2 and is_prime_deterministic(cand): primes.append(cand)
    return primes
def generate_large_prime(bits,method='miller-rabin'):
    if bits<2: raise ValueError("Битность ≥ 2")
    max_allowed=METHOD_MAX_BITS.get(method,1024)
    if bits>max_allowed: raise ValueError(f"Метод '{method}' поддерживает ≤ {max_allowed} бит.")
    while True:
        candidate=secrets.randbits(bits)
        candidate|=(1<<(bits-1))|1
        if any(candidate%p==0 and candidate!=p for p in _SMALL_PRIMES): continue
        if method=='trial':
            if candidate<2 or candidate%2==0: continue
            limit=int(math.isqrt(candidate));f=3
            while f<=limit and candidate%f: f+=2
            if f>limit: return candidate
        elif method=='sieve':
            limit=(1<<bits)-1
            sieve=[True]*(limit+1);sieve[0:2]=[False,False]
            for i in range(2,int(limit**0.5)+1):
                if sieve[i]: sieve[i*i::i]=[False]*((limit-i*i)//i+1)
            primes=[i for i,fl in enumerate(sieve) if fl]
            if primes: return secrets.choice(primes)
        elif method=='genpr':
            m=1<<(bits-1)
            if m%2==0: m+=1
            k=(1<<(bits-1))//2
            primes=genpr_algorithm(m,k)
            if primes: return secrets.choice(primes)
        elif method=='miller-rabin':
            if candidate<(1<<64):
                if is_prime_deterministic(candidate): return candidate
            else:
                if is_prime_miller_rabin(candidate,k=10): return candidate
def mod_exp(base,exp,mod):
    if mod==1: return 0
    result=1;base%=mod
    while exp>0:
        if exp&1: result=(result*base)%mod
        exp>>=1;base=(base*base)%mod
    return result
class GammaTab(QWidget):
    def __init__(self):
        super().__init__()
        layout=QVBoxLayout(self)
        top_bar=QHBoxLayout()
        self.btn_load=QPushButton("📂 Загрузить файл (.txt)")
        self.btn_load.clicked.connect(self.load_file)
        top_bar.addWidget(self.btn_load);top_bar.addStretch();layout.addLayout(top_bar)
        splitter=QSplitter(Qt.Horizontal);layout.addWidget(splitter)
        left_group=QGroupBox("Исходные данные");left_layout=QVBoxLayout(left_group)
        self.input_text=QTextEdit();self.input_text.setPlaceholderText("Введите текст или загрузите файл...");left_layout.addWidget(self.input_text);splitter.addWidget(left_group)
        right_group=QGroupBox("Результат (hex / текст)");right_layout=QVBoxLayout(right_group)
        self.output_text=QTextEdit();self.output_text.setReadOnly(True);right_layout.addWidget(self.output_text);splitter.addWidget(right_group)
        params_group=QGroupBox("Параметры гаммирования");params_layout=QVBoxLayout()
        seed_layout=QHBoxLayout();seed_layout.addWidget(QLabel("Seed (ключ):"));self.seed_input=QLineEdit("12345")
        self.bits_combo=QComboBox();self.bits_combo.addItems(["32","64","128","256"]);self.bits_combo.setCurrentText("128")
        self.btn_gen_seed=QPushButton("🎲 Сгенерировать");self.btn_gen_seed.clicked.connect(self.generate_seed)
        seed_layout.addWidget(self.seed_input);seed_layout.addWidget(QLabel("бит:"));seed_layout.addWidget(self.bits_combo);seed_layout.addWidget(self.btn_gen_seed);params_layout.addLayout(seed_layout)
        gen_layout=QHBoxLayout();gen_layout.addWidget(QLabel("Генератор гаммы:"));self.gen_combo=QComboBox()
        self.gen_combo.addItems(["Линейный конгруэнтный (LCG)","Мультипликативный","Аддитивный (Фибоначчи)"])
        gen_layout.addWidget(self.gen_combo);params_layout.addLayout(gen_layout);params_group.setLayout(params_layout);layout.addWidget(params_group)
        btns_layout=QHBoxLayout();self.btn_encrypt=QPushButton("🔒 Зашифровать");self.btn_decrypt=QPushButton("🔓 Расшифровать")
        self.btn_encrypt.clicked.connect(self.encrypt);self.btn_decrypt.clicked.connect(self.decrypt);btns_layout.addWidget(self.btn_encrypt);btns_layout.addWidget(self.btn_decrypt);layout.addLayout(btns_layout)
        self.btn_save=QPushButton("💾 Сохранить результат");self.btn_save.clicked.connect(self.save_result);layout.addWidget(self.btn_save)
    def generate_seed(self):
        try:
            n_bits=int(self.bits_combo.currentText());seed=secrets.randbits(n_bits);self.seed_input.setText(str(seed))
        except Exception as e: QMessageBox.critical(self,"❌ Ошибка",f"Генерация seed:\n{e}")
    def load_file(self):
        path,_=QFileDialog.getOpenFileName(self,"Открыть TXT","","Text Files (*.txt)")
        if path:
            try:
                with open(path,'r',encoding='utf-8') as f: self.input_text.setPlainText(f.read())
            except Exception as e: QMessageBox.critical(self,"❌ Ошибка",f"Чтение файла:\n{e}")
    def get_generator(self):
        seed=int(self.seed_input.text());typ=self.gen_combo.currentIndex()
        if typ==0: return LCG(seed)
        if typ==1: return Multiplicative(seed)
        return Additive(seed,seed+1)
    def encrypt(self):
        try:
            text=self.input_text.toPlainText()
            if not text: raise ValueError("Введите текст")
            gen=self.get_generator();enc=apply_gamma(text.encode('utf-8'),gen)
            self.output_text.setPlainText(enc.hex());QMessageBox.information(self,"✅ Успех","Текст зашифрован (HEX справа).")
        except Exception as e: QMessageBox.critical(self,"❌ Шифрование",str(e))
    def decrypt(self):
        try:
            txt=self.input_text.toPlainText()
            if not txt: raise ValueError("Введите шифротекст (hex или текст)")
            try: data=bytes.fromhex(txt)
            except ValueError: data=txt.encode('utf-8')
            gen=self.get_generator();dec=apply_gamma(data,gen)
            self.output_text.setPlainText(dec.decode('utf-8',errors='replace'));QMessageBox.information(self,"✅ Успех","Текст расшифрован.")
        except Exception as e: QMessageBox.critical(self,"❌ Дешифрование",str(e))
    def save_result(self):
        text=self.output_text.toPlainText()
        if not text: QMessageBox.warning(self,"⚠️ Пусто","Нет данных для сохранения.")
        else:
            path,_=QFileDialog.getSaveFileName(self,"Сохранить","","Text Files (*.txt)")
            if path:
                try:
                    with open(path,'w',encoding='utf-8') as f: f.write(text)
                    QMessageBox.information(self,"✅ Сохранено",f"Файл:\n{path}")
                except Exception as e: QMessageBox.critical(self,"❌ Ошибка",f"Запись:\n{e}")
class ModArithmeticTab(QWidget):
    def __init__(self):
        super().__init__()
        layout=QVBoxLayout(self)
        params_group=QGroupBox("Генерация двух простых чисел");params_layout=QHBoxLayout()
        params_layout.addWidget(QLabel("Битность:"));self.bits_spin=QSpinBox();self.bits_spin.setRange(8,1024);self.bits_spin.setValue(128);params_layout.addWidget(self.bits_spin)
        params_layout.addWidget(QLabel("Метод:"));self.method_combo=QComboBox()
        self.method_combo.addItems(["Миллер–Рабин (рекомендуется)","Перебор (до 32 бит)","Решето Эратосфена (до 20 бит)","GENPR (до 24 бит)"])
        self.method_combo.currentIndexChanged.connect(self.adjust_bits_limit);params_layout.addWidget(self.method_combo)
        self.btn_gen=QPushButton("🎲 Сгенерировать 2 простых");self.btn_gen.clicked.connect(self.generate_primes);params_layout.addWidget(self.btn_gen)
        params_group.setLayout(params_layout);layout.addWidget(params_group)
        primes_layout=QHBoxLayout();self.p1_edit=QLineEdit();self.p1_edit.setPlaceholderText("p1");self.p2_edit=QLineEdit();self.p2_edit.setPlaceholderText("p2")
        primes_layout.addWidget(self.p1_edit);primes_layout.addWidget(self.p2_edit);layout.addLayout(primes_layout)
        ops_group=QGroupBox("Операции: a, b, n, m");ops_layout=QVBoxLayout();row1=QHBoxLayout()
        row1.addWidget(QLabel("a ="));self.a_edit=QLineEdit();row1.addWidget(self.a_edit);row1.addWidget(QLabel("b ="));self.b_edit=QLineEdit();row1.addWidget(self.b_edit);ops_layout.addLayout(row1)
        row2=QHBoxLayout();row2.addWidget(QLabel("n ="));self.n_edit=QLineEdit("17");row2.addWidget(self.n_edit);row2.addWidget(QLabel("m ="));self.m_edit=QLineEdit("101");row2.addWidget(self.m_edit);ops_layout.addLayout(row2)
        ops_group.setLayout(ops_layout);layout.addWidget(ops_group)
        btns_layout=QHBoxLayout();self.btn_use=QPushButton("→ Использовать p1, p2 как a, b");self.btn_calc=QPushButton("🔢 Выполнить операции")
        self.btn_use.clicked.connect(self.use_primes);self.btn_calc.clicked.connect(self.calculate_all);btns_layout.addWidget(self.btn_use);btns_layout.addWidget(self.btn_calc);layout.addLayout(btns_layout)
        self.results=QTextEdit();self.results.setReadOnly(True);self.results.setPlaceholderText("Результаты...");layout.addWidget(self.results)
        footer=QHBoxLayout();self.btn_export=QPushButton("💾 Сохранить");self.btn_clear=QPushButton("🗑 Очистить")
        self.btn_export.clicked.connect(self.export);self.btn_clear.clicked.connect(self.results.clear);footer.addWidget(self.btn_export);footer.addWidget(self.btn_clear);layout.addLayout(footer)
    def adjust_bits_limit(self):
        method=self.get_method();max_bits=METHOD_MAX_BITS.get(method,1024)
        if self.bits_spin.value()>max_bits:
            self.bits_spin.setValue(max_bits);QMessageBox.information(self,"ℹ️ Ограничение",f"Для метода '{method}' максимум {max_bits} бит. Скорректировано.")
        self.bits_spin.setMaximum(max_bits)
    def get_method(self):
        t=self.method_combo.currentText()
        if "Миллер" in t: return "miller-rabin"
        if "Перебор" in t: return "trial"
        if "Решето" in t: return "sieve"
        if "GENPR" in t: return "genpr"
        return "miller-rabin"
    def generate_primes(self):
        try:
            bits=self.bits_spin.value();method=self.get_method()
            p1=generate_large_prime(bits,method);p2=generate_large_prime(bits,method)
            while p1==p2: p2=generate_large_prime(bits,method)
            self.p1_edit.setText(str(p1));self.p2_edit.setText(str(p2))
            QMessageBox.information(self,"✅ Успех",f"Сгенерированы два простых по {bits} бит (метод: {method}).")
        except Exception as e: QMessageBox.critical(self,"❌ Генерация",str(e))
    def use_primes(self):
        try:
            p1=self.p1_edit.text();p2=self.p2_edit.text()
            if not p1 or not p2: raise ValueError("Сначала сгенерируйте простые.")
            self.a_edit.setText(p1);self.b_edit.setText(p2)
        except Exception as e: QMessageBox.warning(self,"⚠️ Ошибка",str(e))
    def calculate_all(self):
        try:
            a=int(self.a_edit.text());b=int(self.b_edit.text());n=int(self.n_edit.text());m=int(self.m_edit.text())
            if b==0: raise ValueError("b не может быть 0.")
            add=a+b;sub=a-b;mul=a*b;div_floor=a//b;modv=a%b;modexp_v=mod_exp(a,n,m)
            try:
                div_float=a/b
                if abs(div_float)>1e300: div_str="слишком большое"
                else:
                    div_str=f"{div_float:.20g}"
                    if '.' not in div_str and 'e' not in div_str: div_str+=".0"
            except Exception: div_str="ошибка"
            report=f"""Операции:
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
        except Exception as e: QMessageBox.critical(self,"❌ Вычисления",str(e))
    def export(self):
        text=self.results.toPlainText().strip()
        if not text: QMessageBox.warning(self,"⚠️ Пусто","Нет данных.");return
        path,_=QFileDialog.getSaveFileName(self,"Сохранить","","Text Files (*.txt)")
        if path:
            try:
                with open(path,'w',encoding='utf-8') as f: f.write(text)
                QMessageBox.information(self,"✅ Сохранено",f"Файл:\n{path}")
            except Exception as e: QMessageBox.critical(self,"❌ Ошибка",f"Запись:\n{e}")
def extended_gcd(a,b):
    if a==0: return b,0,1
    g,x1,y1=extended_gcd(b%a,a);return g,y1-(b//a)*x1,x1
def mod_inverse(a,m):
    g,x,_=extended_gcd(a,m)
    if g!=1: raise ValueError("Обратный элемент не существует.")
    return x%m
def encode_text_to_blocks(text,N):
    data=text.encode('utf-8');length_prefix=len(data).to_bytes(4,'big');payload=length_prefix+data
    block_bytes=max(1,(N.bit_length()-1)//8)
    if block_bytes<=0: raise ValueError("Слишком малый модуль N для кодирования.")
    blocks=[]
    for i in range(0,len(payload),block_bytes):
        chunk=payload[i:i+block_bytes]
        if len(chunk)<block_bytes: chunk=chunk+b'\x00'*(block_bytes-len(chunk))
        blocks.append(int.from_bytes(chunk,'big'))
    return blocks,block_bytes
def decode_blocks_to_text(blocks,block_bytes):
    if block_bytes<=0: raise ValueError("Некорректный размер блока.")
    data=bytearray()
    for block in blocks: data.extend(block.to_bytes(block_bytes,'big'))
    if len(data)<4: raise ValueError("Недостаточно данных для восстановления длины сообщения.")
    msg_len=int.from_bytes(data[:4],'big');payload=data[4:4+msg_len]
    return payload.decode('utf-8',errors='replace')
def parse_numbers(text):
    if not text.strip(): return []
    cleaned=text.strip()
    for ch in '[]{}()': cleaned=cleaned.replace(ch,' ')
    cleaned=cleaned.replace(';',' ').replace(',',' ')
    parts=[p for p in cleaned.split() if p];nums=[]
    for p in parts:
        if not p.isdigit(): raise ValueError(f"Некорректный элемент списка: '{p}'")
        nums.append(int(p))
    return nums
class RSATab(QWidget):
    def __init__(self):
        super().__init__()
        outer=QVBoxLayout(self)
        gen_group=QGroupBox("1. Генерация двух простых чисел p и q");gen_layout=QVBoxLayout()
        method_row=QHBoxLayout();method_row.addWidget(QLabel("Способ генерации:"))
        self.gen_method_combo=QComboBox()
        self.gen_method_combo.addItems(["Автоматически (одинаковые параметры для p и q)","Автоматически (разные параметры для p и q)","Ввести вручную"])
        self.gen_method_combo.currentIndexChanged.connect(self.on_generation_method_changed)
        method_row.addWidget(self.gen_method_combo);method_row.addStretch();gen_layout.addLayout(method_row)
        params_row=QHBoxLayout()
        self.bits_p_label=QLabel("Битность p:");params_row.addWidget(self.bits_p_label)
        self.bits_p_spin=QSpinBox();self.bits_p_spin.setRange(8,512);self.bits_p_spin.setValue(16);params_row.addWidget(self.bits_p_spin)
        self.method_p_label=QLabel("Метод p:");params_row.addWidget(self.method_p_label)
        self.method_p_combo=QComboBox()
        self.method_p_combo.addItems(["Автоматически","Миллер–Рабин (рекомендуется)","Перебор (до 32 бит)","Решето Эратосфена (до 20 бит)","GENPR (до 24 бит)"])
        params_row.addWidget(self.method_p_combo)
        self.bits_q_label=QLabel("Битность q:");params_row.addWidget(self.bits_q_label)
        self.bits_q_spin=QSpinBox();self.bits_q_spin.setRange(8,512);self.bits_q_spin.setValue(16);params_row.addWidget(self.bits_q_spin)
        self.method_q_label=QLabel("Метод q:");params_row.addWidget(self.method_q_label)
        self.method_q_combo=QComboBox()
        self.method_q_combo.addItems(["Автоматически","Миллер–Рабин (рекомендуется)","Перебор (до 32 бит)","Решето Эратосфена (до 20 бит)","GENPR (до 24 бит)"])
        params_row.addWidget(self.method_q_combo)
        self.method_info_label=QLabel("Метод: выбирается автоматически");params_row.addWidget(self.method_info_label);params_row.addStretch()
        self.btn_gen_pq=QPushButton("🎲 Сгенерировать p, q");self.btn_gen_pq.clicked.connect(self.generate_pq);params_row.addWidget(self.btn_gen_pq)
        gen_layout.addLayout(params_row)
        pq_row=QHBoxLayout();pq_row.addWidget(QLabel("p:"));self.p_edit=QLineEdit();self.p_edit.setPlaceholderText("Введите или сгенерируйте p");pq_row.addWidget(self.p_edit)
        pq_row.addWidget(QLabel("q:"));self.q_edit=QLineEdit();self.q_edit.setPlaceholderText("Введите или сгенерируйте q");pq_row.addWidget(self.q_edit);gen_layout.addLayout(pq_row)
        gen_group.setLayout(gen_layout);outer.addWidget(gen_group)
        key_group=QGroupBox("2. Ключи RSA");key_layout=QVBoxLayout()
        key_mode_row=QHBoxLayout();key_mode_row.addWidget(QLabel("Режим:"));self.key_mode_combo=QComboBox()
        self.key_mode_combo.addItems(["Рассчитать из p и q","Ввести ключи вручную"]);self.key_mode_combo.currentIndexChanged.connect(self.on_key_mode_changed)
        key_mode_row.addWidget(self.key_mode_combo);key_mode_row.addStretch();key_layout.addLayout(key_mode_row)
        calc_row1=QHBoxLayout();calc_row1.addWidget(QLabel("e:"));self.e_edit=QLineEdit("65537")
        self.btn_calc_keys=QPushButton("🔑 Рассчитать ключи");self.btn_calc_keys.clicked.connect(self.calculate_keys)
        calc_row1.addWidget(self.e_edit);calc_row1.addWidget(self.btn_calc_keys);calc_row1.addStretch()
        self.calc_keys_widget=QWidget();calc_keys_layout=QVBoxLayout(self.calc_keys_widget);calc_keys_layout.addLayout(calc_row1);key_layout.addWidget(self.calc_keys_widget)
        manual_keys_widget=QWidget();manual_keys_layout=QVBoxLayout(manual_keys_widget);manual_row1=QHBoxLayout()
        manual_row1.addWidget(QLabel("N:"));self.N_edit=QLineEdit();self.N_edit.setPlaceholderText("Введите N (модуль)");manual_row1.addWidget(self.N_edit)
        manual_row1.addWidget(QLabel("e:"));self.e_manual_edit=QLineEdit("65537");self.e_manual_edit.setPlaceholderText("Введите e (открытая экспонента)");manual_row1.addWidget(self.e_manual_edit);manual_keys_layout.addLayout(manual_row1)
        manual_row2=QHBoxLayout();manual_row2.addWidget(QLabel("d:"));self.d_edit=QLineEdit();self.d_edit.setPlaceholderText("Введите d (секретная экспонента)");manual_row2.addWidget(self.d_edit)
        self.btn_set_manual_keys=QPushButton("✅ Установить ключи");self.btn_set_manual_keys.clicked.connect(self.set_manual_keys);manual_row2.addWidget(self.btn_set_manual_keys);manual_row2.addStretch();manual_keys_layout.addLayout(manual_row2)
        self.manual_keys_widget=manual_keys_widget;self.manual_keys_widget.setVisible(False);key_layout.addWidget(self.manual_keys_widget)
        display_row=QHBoxLayout();self.N_label=QLabel("N = ?");self.phi_label=QLabel("φ(N) = ?");self.d_label=QLabel("d = ?")
        display_row.addWidget(self.N_label);display_row.addWidget(self.phi_label);display_row.addWidget(self.d_label);display_row.addStretch();key_layout.addLayout(display_row)
        key_file_row=QHBoxLayout();self.btn_load_keys=QPushButton("📥 Загрузить ключи из файла");self.btn_load_keys.clicked.connect(self.load_keys_from_file)
        self.btn_save_keys=QPushButton("💾 Сохранить ключи в файл");self.btn_save_keys.clicked.connect(self.save_keys_to_file)
        key_file_row.addWidget(self.btn_load_keys);key_file_row.addWidget(self.btn_save_keys);key_file_row.addStretch();key_layout.addLayout(key_file_row)
        key_group.setLayout(key_layout);outer.addWidget(key_group)
        data_group=QGroupBox("3. Входные и выходные данные");data_layout=QVBoxLayout()
        splitter=QSplitter(Qt.Horizontal)
        left_group=QGroupBox("Входные данные");left_layout=QVBoxLayout(left_group)
        self.input_text_edit=QTextEdit()
        self.input_text_edit.setPlaceholderText("Введите текст (А-Я и пробел) или блоки/шифр.")
        left_layout.addWidget(self.input_text_edit)
        left_btns=QHBoxLayout();self.btn_load_input=QPushButton("📥 Загрузить из файла");self.btn_load_input.clicked.connect(self.load_input_data)
        self.btn_clear_input=QPushButton("🗑 Очистить");self.btn_clear_input.clicked.connect(self.input_text_edit.clear)
        left_btns.addWidget(self.btn_load_input);left_btns.addWidget(self.btn_clear_input);left_btns.addStretch();left_layout.addLayout(left_btns);splitter.addWidget(left_group)
        right_group=QGroupBox("Выходные данные");right_layout=QVBoxLayout(right_group)
        self.output_text_edit=QTextEdit();self.output_text_edit.setReadOnly(False);self.output_text_edit.setPlaceholderText("Результат...");right_layout.addWidget(self.output_text_edit)
        right_btns=QHBoxLayout();self.btn_save_output=QPushButton("💾 Сохранить в файл");self.btn_save_output.clicked.connect(self.save_output_data)
        self.btn_clear_output=QPushButton("🗑 Очистить");self.btn_clear_output.clicked.connect(self.output_text_edit.clear)
        self.btn_copy_output=QPushButton("📋 Копировать");self.btn_copy_output.clicked.connect(self.copy_output)
        right_btns.addWidget(self.btn_save_output);right_btns.addWidget(self.btn_clear_output);right_btns.addWidget(self.btn_copy_output);right_btns.addStretch();right_layout.addLayout(right_btns);splitter.addWidget(right_group)
        splitter.setSizes([400,400]);data_layout.addWidget(splitter)
        log_group=QGroupBox("Лог операций");log_layout=QVBoxLayout(log_group);self.log_text_edit=QTextEdit()
        self.log_text_edit.setReadOnly(True);self.log_text_edit.setPlaceholderText("Логи...");log_layout.addWidget(self.log_text_edit);data_layout.addWidget(log_group)
        ops_row=QHBoxLayout();self.btn_encrypt=QPushButton("🔒 Зашифровать");self.btn_encrypt.clicked.connect(self.encrypt_rsa)
        self.btn_decrypt=QPushButton("🔓 Расшифровать");self.btn_decrypt.clicked.connect(self.decrypt_rsa)
        ops_row.addWidget(self.btn_encrypt);ops_row.addWidget(self.btn_decrypt);ops_row.addStretch();data_layout.addLayout(ops_row)
        data_group.setLayout(data_layout);outer.addWidget(data_group)
        self.N=None;self.phi=None;self.d=None;self.e_val=65537;self.blocks=[];self.block_bytes=None;self.cipher_blocks=[]
        self.last_cipher_payload=None;self.last_output_kind=None
        self.on_key_mode_changed(0);self.on_generation_method_changed(0)
        self.bits_p_spin.valueChanged.connect(self.update_auto_method_label)
        self.bits_q_spin.valueChanged.connect(self.update_auto_method_label)
        self.method_p_combo.currentIndexChanged.connect(self.update_auto_method_label)
        self.method_q_combo.currentIndexChanged.connect(self.update_auto_method_label)
        self.update_auto_method_label();self.btn_encrypt.setEnabled(True);self.btn_decrypt.setEnabled(True)
    def detect_input_type(self,content):
        if not content or not content.strip(): return 'empty'
        content=content.strip();allowed_separators=set("[]{}(),; \t\r\n")
        if any(not (ch.isdigit() or ch in allowed_separators) for ch in content): return 'text'
        try:
            blocks=parse_numbers(content)
            if blocks and len(blocks)>0: return 'blocks'
        except (ValueError,AttributeError): pass
        return 'text'
    def auto_select_method(self,bits:int,combo)->str:
        if combo is not None and combo.currentIndex()>0:
            idx=combo.currentIndex()
            if idx==1: return "miller-rabin"
            if idx==2: return "trial"
            if idx==3: return "sieve"
            if idx==4: return "genpr"
        if bits<=METHOD_MAX_BITS.get("sieve",0): return "sieve"
        if bits<=METHOD_MAX_BITS.get("genpr",0): return "genpr"
        if bits<=METHOD_MAX_BITS.get("trial",0): return "trial"
        return "miller-rabin"
    def update_auto_method_label(self):
        bits_p=self.bits_p_spin.value();bits_q=self.bits_q_spin.value()
        method_p=self.auto_select_method(bits_p,self.method_p_combo);method_q=self.auto_select_method(bits_q,self.method_q_combo)
        name_map={"miller-rabin":"Миллер–Рабин","trial":"Перебор","sieve":"Решето Эратосфена","genpr":"GENPR"}
        base=f"Метод p: {name_map.get(method_p,method_p)}; Метод q: {name_map.get(method_q,method_q)}"
        if self.method_p_combo.currentIndex()==0 and self.method_q_combo.currentIndex()==0: base+=" (автовыбор по битности)"
        self.method_info_label.setText(base)
    def on_generation_method_changed(self,index):
        if index==2:
            self.btn_gen_pq.setEnabled(False);self.bits_p_spin.setEnabled(False);self.bits_q_spin.setEnabled(False)
            self.method_p_combo.setEnabled(False);self.method_q_combo.setEnabled(False)
            self.bits_q_label.setVisible(True);self.bits_q_spin.setVisible(True);self.method_q_label.setVisible(True);self.method_q_combo.setVisible(True)
            self.method_info_label.setVisible(True);self.method_info_label.setText("Режим: ввод p и q вручную");return
        self.btn_gen_pq.setEnabled(True);self.bits_p_spin.setEnabled(True);self.method_p_combo.setEnabled(True);self.method_info_label.setVisible(True)
        if index==0:
            self.bits_q_label.setVisible(False);self.bits_q_spin.setVisible(False);self.method_q_label.setVisible(False);self.method_q_combo.setVisible(False)
            self.bits_q_spin.setValue(self.bits_p_spin.value());self.method_q_combo.setCurrentIndex(self.method_p_combo.currentIndex())
        else:
            self.bits_q_label.setVisible(True);self.bits_q_spin.setVisible(True);self.method_q_label.setVisible(True);self.method_q_combo.setVisible(True)
            self.bits_q_spin.setEnabled(True);self.method_q_combo.setEnabled(True)
        self.update_auto_method_label()
    def generate_pq(self):
        try:
            gen_method=self.gen_method_combo.currentIndex()
            if gen_method==2:
                self.log_text_edit.append("[Генерация]\nРежим 'Ввести вручную': введите значения p и q вручную.");return
            bits_p=self.bits_p_spin.value()
            if gen_method==0:
                bits_q=bits_p;method_p=self.auto_select_method(bits_p,self.method_p_combo);method_q=method_p
            else:
                bits_q=self.bits_q_spin.value();method_p=self.auto_select_method(bits_p,self.method_p_combo);method_q=self.auto_select_method(bits_q,self.method_q_combo)
            p=generate_large_prime(bits_p,method_p);q=generate_large_prime(bits_q,method_q);attempts=1
            while p==q and attempts<10:
                q=generate_large_prime(bits_q,method_q);attempts+=1
            if p==q: raise ValueError("Не удалось сгенерировать различные простые числа.")
            self.p_edit.setText(str(p));self.q_edit.setText(str(q))
            self.log_text_edit.append(f"[Генерация простых чисел]\nМетод генерации: {self.gen_method_combo.currentText()}\nБитность p: {bits_p} (метод: {method_p})\nБитность q: {bits_q} (метод: {method_q})\np = {p}\nq = {q}\np × q = {p*q}\n")
        except Exception as e: QMessageBox.critical(self,"❌ Генерация",str(e))
    def calculate_keys(self):
        try:
            p_text=self.p_edit.text().strip();q_text=self.q_edit.text().strip()
            if not p_text or not q_text: raise ValueError("Введите или сгенерируйте p и q.")
            p=int(p_text);q=int(q_text);e_val=int(self.e_edit.text())
            if p<2 or q<2: raise ValueError("p и q должны быть простыми числами (≥ 2).")
            if p==q: raise ValueError("p и q должны быть различны.")
            self.N=p*q;self.phi=(p-1)*(q-1)
            if e_val<=1 or e_val>=self.phi: raise ValueError(f"e должно быть в диапазоне (1, φ(N)={self.phi}).")
            g,_,_=extended_gcd(e_val,self.phi)
            if g!=1:
                e_found=None
                for cand in [3,5,17,257,65537]:
                    if 1<cand<self.phi and extended_gcd(cand,self.phi)[0]==1: e_found=cand;break
                if e_found:
                    e_val=e_found;self.e_edit.setText(str(e_val))
                    self.log_text_edit.append(f"[Ключи] Введённое e не взаимно просто с φ(N). Автоматически выбрано e = {e_val}.")
                else: raise ValueError(f"Введенное e={e_val} не взаимно просто с φ(N)={self.phi}.")
            self.e_val=e_val;self.d=mod_inverse(e_val,self.phi)
            self.N_label.setText(f"N = {self.N}");self.phi_label.setText(f"φ(N) = {self.phi}");self.d_label.setText(f"d = {self.d}")
            self.block_bytes=None;self.blocks=[];self.cipher_blocks=[];self.last_output_kind=None;self.last_cipher_payload=None
            self.log_text_edit.append(f"[Ключи вычислены]\np = {p}\nq = {q}\nN = p × q = {self.N}\nφ(N) = (p-1) × (q-1) = {self.phi}\ne = {e_val}\nd = e⁻¹ mod φ(N) = {self.d}\nОткрытый ключ: (N={self.N}, e={e_val})\nСекретный ключ: d={self.d}\n")
        except Exception as e: QMessageBox.critical(self,"❌ Расчёт",str(e))
    def on_key_mode_changed(self,index):
        if index==0:
            self.calc_keys_widget.setVisible(True);self.manual_keys_widget.setVisible(False)
        else:
            self.calc_keys_widget.setVisible(False);self.manual_keys_widget.setVisible(True)
    def set_manual_keys(self):
        try:
            N_text=self.N_edit.text().strip();e_text=self.e_manual_edit.text().strip();d_text=self.d_edit.text().strip()
            if not N_text: raise ValueError("Введите N (модуль).")
            if not e_text: raise ValueError("Введите e (открытая экспонента).")
            if not d_text: raise ValueError("Введите d (секретная экспонента).")
            N=int(N_text);e_val=int(e_text);d_val=int(d_text)
            if N<2: raise ValueError("N должно быть ≥ 2.")
            if e_val<=1: raise ValueError("e должно быть > 1.")
            if d_val<=1: raise ValueError("d должно быть > 1.")
            self.N=N;self.e_val=e_val;self.d=d_val
            self.N_label.setText(f"N = {self.N}");self.phi_label.setText("φ(N) = ? (неизвестно)");self.d_label.setText(f"d = {self.d}")
            self.block_bytes=None;self.blocks=[];self.cipher_blocks=[];self.last_output_kind=None;self.last_cipher_payload=None
            self.e_edit.setText(str(e_val))
            self.log_text_edit.append(f"[Ключи установлены вручную]\nN = {self.N}\ne = {e_val}\nd = {d_val}\n")
        except Exception as e: QMessageBox.critical(self,"❌ Ошибка",str(e))
    def load_keys_from_file(self):
        path,_=QFileDialog.getOpenFileName(self,"Загрузить ключи","","Text Files (*.txt);;All Files (*)")
        if path:
            try:
                with open(path,'r',encoding='utf-8') as f: content=f.read().strip()
                if not content:
                    QMessageBox.warning(self,"⚠️ Пусто","Файл пуст.");return
                lines=content.split('\n');N_val=None;e_val=None;d_val=None
                for line in lines:
                    line=line.strip()
                    if not line or line.startswith('#'): continue
                    if '=' in line:
                        key,value=line.split('=',1);key=key.strip().lower();value=value.strip()
                        try:
                            if key=='n': N_val=int(value)
                            elif key=='e': e_val=int(value)
                            elif key=='d': d_val=int(value)
                        except ValueError: continue
                    else:
                        try:
                            num=int(line)
                            if N_val is None: N_val=num
                            elif e_val is None: e_val=num
                            elif d_val is None: d_val=num
                        except ValueError: continue
                if N_val is None or e_val is None or d_val is None:
                    QMessageBox.warning(self,"⚠️ Ошибка","Не удалось распарсить ключи из файла.");return
                self.N_edit.setText(str(N_val));self.e_manual_edit.setText(str(e_val));self.d_edit.setText(str(d_val));self.set_manual_keys()
                self.log_text_edit.append(f"[Ключи] Загружены из файла: {path}")
            except Exception as e: QMessageBox.critical(self,"❌ Ошибка",f"Ошибка загрузки:\n{e}")
    def save_keys_to_file(self):
        if self.N is None or self.e_val is None or self.d is None:
            QMessageBox.warning(self,"⚠️ Ошибка","Сначала установите ключи.");return
        path,_=QFileDialog.getSaveFileName(self,"Сохранить ключи","","Text Files (*.txt);;All Files (*)")
        if path:
            try:
                content=f"""RSA Ключи
==========
Открытый ключ:
N = {self.N}
e = {self.e_val}
Секретный ключ:
d = {self.d}
Формат для загрузки:
N={self.N}
e={self.e_val}
d={self.d}
"""
                with open(path,'w',encoding='utf-8') as f: f.write(content)
                self.log_text_edit.append(f"[Ключи] Сохранены в файл: {path}")
            except Exception as e: QMessageBox.critical(self,"❌ Ошибка",f"Ошибка сохранения:\n{e}")
    def encrypt_rsa(self):
        try:
            if self.N is None: raise ValueError("Сначала вычислите ключи (N).")
            content=self.input_text_edit.toPlainText().strip()
            if not content: raise ValueError("Введите данные для шифрования.")
            input_type=self.detect_input_type(content)
            if input_type=='text':
                blocks_to_encrypt,block_bytes=encode_text_to_blocks(content,self.N)
                self.blocks=blocks_to_encrypt;self.block_bytes=block_bytes
            elif input_type=='blocks':
                blocks_to_encrypt=parse_numbers(content)
                if not blocks_to_encrypt: raise ValueError("Не удалось распарсить блоки M_i.")
                invalid_blocks=[m for m in blocks_to_encrypt if m>=self.N]
                if invalid_blocks: raise ValueError(f"Блоки {invalid_blocks} >= N={self.N}.")
                self.blocks=blocks_to_encrypt;self.block_bytes=max(1,(self.N.bit_length()-1)//8)
            else: raise ValueError("Не удалось определить тип данных.")
            e=int(self.e_edit.text())
            if self.phi and (e<=1 or e>=self.phi): raise ValueError(f"e вне диапазона (1, φ(N)={self.phi}).")
            self.cipher_blocks=[mod_exp(m,e,self.N) for m in self.blocks]
            cipher_str=', '.join(map(str,self.cipher_blocks))
            self.output_text_edit.setPlainText(cipher_str)
            self.log_text_edit.append(f"[Шифрование] Блоков: {len(self.cipher_blocks)} ключ (N={self.N}, e={e})")
            self.last_output_kind="cipher";self.last_cipher_payload={"type":"rsa_cipher","cipher":self.cipher_blocks,"block_bytes":self.block_bytes,"N":self.N,"e":e}
        except Exception as e: QMessageBox.critical(self,"❌ Шифрование",str(e))
    def decrypt_rsa(self):
        try:
            if self.N is None or self.d is None: raise ValueError("Сначала вычислите ключи (N и d).")
            content=self.input_text_edit.toPlainText().strip()
            if content:
                input_type=self.detect_input_type(content)
                if input_type=='blocks':
                    cipher_blocks_to_decrypt=parse_numbers(content)
                    if not cipher_blocks_to_decrypt: raise ValueError("Не удалось распарсить блоки C_i.")
                else: raise ValueError("Ожидаются числовые блоки C_i.")
            elif self.cipher_blocks: cipher_blocks_to_decrypt=self.cipher_blocks
            else: raise ValueError("Нет блоков для расшифровки.")
            invalid=[c for c in cipher_blocks_to_decrypt if c>=self.N]
            if invalid: QMessageBox.warning(self,"⚠️ Внимание",f"Есть блоки >= N: {invalid}")
            decrypted=[mod_exp(c,self.d,self.N) for c in cipher_blocks_to_decrypt]
            block_bytes=self.block_bytes or max(1,(self.N.bit_length()-1)//8)
            try: text=decode_blocks_to_text(decrypted,block_bytes)
            except Exception as exc: raise ValueError(f"Ошибка восстановления: {exc}")
            self.output_text_edit.setPlainText(text);self.last_output_kind="plain";self.last_cipher_payload=None;self.block_bytes=block_bytes
            self.log_text_edit.append(f"[Дешифрование] Блоков: {len(cipher_blocks_to_decrypt)} ключ (N={self.N}, d={self.d})")
        except Exception as e: QMessageBox.critical(self,"❌ Дешифрование",str(e))
    def load_input_data(self):
        path,_=QFileDialog.getOpenFileName(self,"Загрузить вход","","Text Files (*.txt);;All Files (*)")
        if path:
            try:
                with open(path,'r',encoding='utf-8') as f: content=f.read().strip()
                if not content: QMessageBox.warning(self,"⚠️ Пусто","Файл пуст.");return
                payload=None
                try: payload=json.loads(content)
                except json.JSONDecodeError: pass
                if isinstance(payload,dict) and payload.get("type")=="rsa_cipher":
                    self.cipher_blocks=payload.get("cipher",[]);self.block_bytes=payload.get("block_bytes");saved_N=payload.get("N")
                    if saved_N and self.N and saved_N!=self.N:
                        QMessageBox.warning(self,"⚠️ Несовпадение","N в файле отличается.")
                    self.input_text_edit.setPlainText(', '.join(map(str,self.cipher_blocks)))
                    self.output_text_edit.setPlainText(payload.get("cipher_text",""))
                    self.last_cipher_payload=payload;self.last_output_kind="cipher"
                    self.log_text_edit.append(f"[Загрузка шифра] {path}")
                    return
                self.input_text_edit.setPlainText(content)
                self.log_text_edit.append(f"[Загрузка входа] {path} ({len(content)} символов)")
            except Exception as e: QMessageBox.critical(self,"❌ Ошибка",f"Загрузка:\n{e}")
    def save_output_data(self):
        content=self.output_text_edit.toPlainText().strip()
        if not content: QMessageBox.warning(self,"⚠️ Пусто","Нет данных для сохранения.");return
        path,_=QFileDialog.getSaveFileName(self,"Сохранить выход","","Text Files (*.txt);;All Files (*)")
        if path:
            try:
                if self.last_output_kind=="cipher" and self.last_cipher_payload:
                    payload=dict(self.last_cipher_payload);payload["cipher_text"]=content
                    with open(path,'w',encoding='utf-8') as f: json.dump(payload,f,ensure_ascii=False,indent=2)
                else:
                    with open(path,'w',encoding='utf-8') as f: f.write(content)
                self.log_text_edit.append(f"[Сохранение выхода] {path}")
            except Exception as e: QMessageBox.critical(self,"❌ Ошибка",f"Сохранение:\n{e}")
    def copy_output(self):
        content=self.output_text_edit.toPlainText()
        if not content: QMessageBox.warning(self,"⚠️ Пусто","Нет данных для копирования.");return
        QApplication.clipboard().setText(content)
class RSALibraryTab(QWidget):
    def __init__(self):
        super().__init__()
        self.private_key=None;self.public_key=None
        outer=QVBoxLayout(self)
        key_group=QGroupBox("1. Ключи RSA (библиотека)");key_layout=QVBoxLayout()
        row=QHBoxLayout();row.addWidget(QLabel("Битность:"));self.lib_bits_spin=QSpinBox();self.lib_bits_spin.setRange(512,4096);self.lib_bits_spin.setValue(2048)
        row.addWidget(self.lib_bits_spin);self.btn_lib_generate=QPushButton("🎲 Сгенерировать пару ключей");self.btn_lib_generate.clicked.connect(self.lib_generate_keys)
        row.addWidget(self.btn_lib_generate);row.addStretch();key_layout.addLayout(row)
        keys_row=QHBoxLayout();self.pub_key_edit=QTextEdit();self.pub_key_edit.setPlaceholderText("Публичный ключ (PEM)")
        self.priv_key_edit=QTextEdit();self.priv_key_edit.setPlaceholderText("Приватный ключ (PEM)")
        keys_row.addWidget(self.pub_key_edit);keys_row.addWidget(self.priv_key_edit);key_layout.addLayout(keys_row)
        key_btns=QHBoxLayout();btn_load_pub=QPushButton("📥 Загрузить публичный ключ");btn_load_pub.clicked.connect(self.lib_load_public_key)
        btn_save_pub=QPushButton("💾 Сохранить публичный ключ");btn_save_pub.clicked.connect(self.lib_save_public_key)
        btn_load_priv=QPushButton("📥 Загрузить приватный ключ");btn_load_priv.clicked.connect(self.lib_load_private_key)
        btn_save_priv=QPushButton("💾 Сохранить приватный ключ");btn_save_priv.clicked.connect(self.lib_save_private_key)
        key_btns.addWidget(btn_load_pub);key_btns.addWidget(btn_save_pub);key_btns.addWidget(btn_load_priv);key_btns.addWidget(btn_save_priv);key_btns.addStretch();key_layout.addLayout(key_btns)
        key_group.setLayout(key_layout);outer.addWidget(key_group)
        data_group=QGroupBox("2. Данные");data_layout=QVBoxLayout()
        splitter=QSplitter(Qt.Horizontal)
        left_box=QGroupBox("Вход (открытый текст ИЛИ Base64 блоки)");left_layout=QVBoxLayout(left_box)
        self.input_edit=QTextEdit();self.input_edit.setPlaceholderText("Вставьте текст для шифрования или многострочный Base64 для расшифровки");left_layout.addWidget(self.input_edit)
        left_btns=QHBoxLayout();self.btn_load_input_lib=QPushButton("📥 Загрузить вход");self.btn_load_input_lib.clicked.connect(self.load_library_input_file)
        self.btn_clear_input_lib=QPushButton("🗑 Очистить вход");self.btn_clear_input_lib.clicked.connect(self.input_edit.clear)
        left_btns.addWidget(self.btn_load_input_lib);left_btns.addWidget(self.btn_clear_input_lib);left_btns.addStretch();left_layout.addLayout(left_btns)
        splitter.addWidget(left_box)
        right_box=QGroupBox("Выход (шифр или расшифрованный текст)");right_layout=QVBoxLayout(right_box)
        self.output_edit=QTextEdit();self.output_edit.setPlaceholderText("Результат будет здесь");right_layout.addWidget(self.output_edit)
        right_btns=QHBoxLayout();self.btn_save_output_lib=QPushButton("💾 Сохранить выход");self.btn_save_output_lib.clicked.connect(self.save_library_output_file)
        self.btn_copy_output_lib=QPushButton("📋 Копировать выход");self.btn_copy_output_lib.clicked.connect(lambda: QApplication.clipboard().setText(self.output_edit.toPlainText()))
        self.btn_clear_output_lib=QPushButton("🗑 Очистить выход");self.btn_clear_output_lib.clicked.connect(self.output_edit.clear)
        right_btns.addWidget(self.btn_save_output_lib);right_btns.addWidget(self.btn_copy_output_lib);right_btns.addWidget(self.btn_clear_output_lib);right_btns.addStretch();right_layout.addLayout(right_btns)
        splitter.addWidget(right_box);splitter.setSizes([450,450]);data_layout.addWidget(splitter)
        btns=QHBoxLayout();self.btn_lib_encrypt=QPushButton("🔒 Зашифровать (OAEP, большие данные)");self.btn_lib_encrypt.clicked.connect(self.lib_encrypt)
        self.btn_lib_decrypt=QPushButton("🔓 Расшифровать (OAEP)");self.btn_lib_decrypt.clicked.connect(self.lib_decrypt)
        btns.addWidget(self.btn_lib_encrypt);btns.addWidget(self.btn_lib_decrypt);btns.addStretch();data_layout.addLayout(btns)
        self.lib_status_label=QLabel("Готово.");data_layout.addWidget(self.lib_status_label)
        data_group.setLayout(data_layout);outer.addWidget(data_group)
    def set_status(self,text): self.lib_status_label.setText(text)
    def ensure_public_key(self):
        if self.public_key: return self.public_key
        pem=self.pub_key_edit.toPlainText().strip()
        if not pem: raise ValueError("Публичный ключ не задан.")
        self.public_key=serialization.load_pem_public_key(pem.encode('utf-8'));return self.public_key
    def ensure_private_key(self):
        if self.private_key: return self.private_key
        pem=self.priv_key_edit.toPlainText().strip()
        if not pem: raise ValueError("Приватный ключ не задан.")
        self.private_key=serialization.load_pem_private_key(pem.encode('utf-8'),password=None);return self.private_key
    def lib_generate_keys(self):
        try:
            bits=self.lib_bits_spin.value()
            private_key=crypto_rsa.generate_private_key(public_exponent=65537,key_size=bits)
            public_key=private_key.public_key()
            priv_pem=private_key.private_bytes(serialization.Encoding.PEM,serialization.PrivateFormat.TraditionalOpenSSL,serialization.NoEncryption()).decode('utf-8')
            pub_pem=public_key.public_bytes(serialization.Encoding.PEM,serialization.PublicFormat.SubjectPublicKeyInfo).decode('utf-8')
            self.private_key=private_key;self.public_key=public_key
            self.priv_key_edit.setPlainText(priv_pem);self.pub_key_edit.setPlainText(pub_pem)
            self.set_status(f"Новая пара ключей ({bits} бит) создана.")
        except Exception as e: QMessageBox.critical(self,"❌ Ошибка",str(e))
    def lib_load_public_key(self):
        path,_=QFileDialog.getOpenFileName(self,"Загрузить публичный ключ","","PEM Files (*.pem);;All Files (*)")
        if path:
            try:
                with open(path,'r',encoding='utf-8') as f: pem=f.read()
                self.pub_key_edit.setPlainText(pem);self.public_key=serialization.load_pem_public_key(pem.encode('utf-8'))
                self.set_status(f"Публичный ключ загружен из {path}.")
            except Exception as e: QMessageBox.critical(self,"❌ Ошибка",f"Не удалось загрузить ключ:\n{e}")
    def lib_save_public_key(self):
        pem=self.pub_key_edit.toPlainText().strip()
        if not pem: QMessageBox.warning(self,"⚠️ Пусто","Нет публичного ключа.");return
        path,_=QFileDialog.getSaveFileName(self,"Сохранить публичный ключ","","PEM Files (*.pem);;All Files (*)")
        if path:
            try:
                with open(path,'w',encoding='utf-8') as f: f.write(pem)
                self.set_status(f"Публичный ключ сохранён в {path}.")
            except Exception as e: QMessageBox.critical(self,"❌ Ошибка",f"Не удалось сохранить ключ:\n{e}")
    def lib_load_private_key(self):
        path,_=QFileDialog.getOpenFileName(self,"Загрузить приватный ключ","","PEM Files (*.pem);;All Files (*)")
        if path:
            try:
                with open(path,'r',encoding='utf-8') as f: pem=f.read()
                self.priv_key_edit.setPlainText(pem);self.private_key=serialization.load_pem_private_key(pem.encode('utf-8'),password=None)
                self.set_status(f"Приватный ключ загружен из {path}.")
            except Exception as e: QMessageBox.critical(self,"❌ Ошибка",f"Не удалось загрузить ключ:\n{e}")
    def lib_save_private_key(self):
        pem=self.priv_key_edit.toPlainText().strip()
        if not pem: QMessageBox.warning(self,"⚠️ Пусто","Нет приватного ключа.");return
        path,_=QFileDialog.getSaveFileName(self,"Сохранить приватный ключ","","PEM Files (*.pem);;All Files (*)")
        if path:
            try:
                with open(path,'w',encoding='utf-8') as f: f.write(pem)
                self.set_status(f"Приватный ключ сохранён в {path}.")
            except Exception as e: QMessageBox.critical(self,"❌ Ошибка",f"Не удалось сохранить ключ:\n{e}")
    def _chunk_encrypt(self,public_key,data_bytes,hash_alg=hashes.SHA256()):
        key_bytes=public_key.key_size//8;h_len=hash_alg.digest_size
        max_chunk=key_bytes-2*h_len-2
        if max_chunk<=0: raise ValueError("Недостаточный размер ключа для OAEP.")
        chunks=[data_bytes[i:i+max_chunk] for i in range(0,len(data_bytes),max_chunk)]
        enc_chunks=[]
        for ch in chunks:
            enc=public_key.encrypt(ch,crypto_padding.OAEP(mgf=crypto_padding.MGF1(algorithm=hash_alg),algorithm=hash_alg,label=None))
            enc_chunks.append(base64.b64encode(enc).decode('utf-8'))
        return enc_chunks,max_chunk
    def _chunk_decrypt(self,private_key,cipher_text,hash_alg=hashes.SHA256()):
        lines=[l.strip() for l in cipher_text.replace('\r','').split('\n') if l.strip()]
        if not lines: raise ValueError("Нет данных для расшифровки.")
        out=bytearray()
        for line in lines:
            enc=base64.b64decode(line)
            dec=private_key.decrypt(enc,crypto_padding.OAEP(mgf=crypto_padding.MGF1(algorithm=hash_alg),algorithm=hash_alg,label=None))
            out.extend(dec)
        return out
    def lib_encrypt(self):
        try:
            public_key=self.ensure_public_key()
            text=self.input_edit.toPlainText()
            if not text: raise ValueError("Введите текст для шифрования в левое поле.")
            data=text.encode('utf-8')
            enc_chunks,_=self._chunk_encrypt(public_key,data)
            self.output_edit.setPlainText('\n'.join(enc_chunks))
            self.set_status(f"Текст зашифрован: {len(enc_chunks)} блок(ов).")
        except ValueError as ve:
            QMessageBox.critical(self,"❌ Ошибка",str(ve))
        except Exception as e:
            QMessageBox.critical(self,"❌ Ошибка",f"Encryption failed: {e}")
    def lib_decrypt(self):
        try:
            private_key=self.ensure_private_key()
            cipher_text=self.input_edit.toPlainText().strip()
            if not cipher_text: raise ValueError("Введите Base64 блоки шифра в левое поле.")
            lines=[l for l in cipher_text.splitlines() if l.strip()]
            for ln in lines:
                try: base64.b64decode(ln)
                except Exception: raise ValueError("Обнаружена строка, не похожая на Base64.")
            data=self._chunk_decrypt(private_key,cipher_text)
            self.output_edit.setPlainText(data.decode('utf-8',errors='replace'))
            self.set_status("Шифротекст расшифрован.")
        except ValueError as ve:
            QMessageBox.critical(self,"❌ Ошибка",str(ve))
        except Exception as e:
            QMessageBox.critical(self,"❌ Ошибка",f"Decryption failed: {e}")
    def load_library_input_file(self):
        path,_=QFileDialog.getOpenFileName(self,"Загрузить вход","","Text Files (*.txt);;All Files (*)")
        if path:
            try:
                with open(path,'r',encoding='utf-8') as f: content=f.read()
                if not content.strip(): QMessageBox.warning(self,"⚠️ Пусто","Файл пуст.");return
                self.input_edit.setPlainText(content)
                self.set_status(f"Вход загружен из {path}")
            except Exception as e: QMessageBox.critical(self,"❌ Ошибка",f"Загрузка входа:\n{e}")
    def save_library_output_file(self):
        content=self.output_edit.toPlainText().strip()
        if not content: QMessageBox.warning(self,"⚠️ Пусто","Нет данных для сохранения.");return
        path,_=QFileDialog.getSaveFileName(self,"Сохранить выход","","Text Files (*.txt);;All Files (*)")
        if path:
            try:
                # если это многострочный Base64 – сохраняем как есть
                with open(path,'w',encoding='utf-8') as f: f.write(content)
                self.set_status(f"Выход сохранён в {path}")
            except Exception as e: QMessageBox.critical(self,"❌ Ошибка",f"Сохранение выхода:\n{e}")
class CryptoSuite(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Криптографический практикум (ПЗ-9, ПЗ-10, ПЗ-11)")
        self.resize(1200,800);self.current_theme="light"
        central=QWidget();self.setCentralWidget(central);layout=QVBoxLayout(central)
        tabs=QTabWidget();tabs.addTab(GammaTab(),"🔒 ПЗ-9: Гаммирование");tabs.addTab(ModArithmeticTab(),"🧮 ПЗ-10: Модулярная арифметика")
        tabs.addTab(RSATab(),"🔐 ПЗ-11: RSA");tabs.addTab(RSALibraryTab(),"🔐 ПЗ-12: RSA (библиотека)");layout.addWidget(tabs)
        self.apply_style_light();self.create_menu()
    def create_menu(self):
        menubar=QMenuBar(self);view_menu=menubar.addMenu("Вид")
        act_light=QAction("Светлая тема",self);act_dark=QAction("Тёмная тема",self)
        act_light.triggered.connect(self.apply_style_light);act_dark.triggered.connect(self.apply_style_dark)
        view_menu.addAction(act_light);view_menu.addAction(act_dark);self.setMenuBar(menubar)
    def apply_common_styles(self):
        font=QFont("Segoe UI",10);self.setFont(font)
        self.setStyleSheet(self.styleSheet()+"""
            QGroupBox {border:1px solid #b0b0b0;border-radius:8px;margin-top:12px;padding:8px;font-weight:bold;}
            QGroupBox::title {subcontrol-origin: margin;subcontrol-position: top left;padding:0 6px;}
            QPushButton {padding:6px 12px;border-radius:6px;font-weight:500;}
            QLineEdit, QTextEdit, QSpinBox, QComboBox {border:1px solid #b8b8b8;border-radius:6px;padding:4px;}
            QTabBar::tab {padding:6px 14px;margin:4px;border-radius:6px;font-weight:500;}
            QTabWidget::pane {border:1px solid #b0b0b0;}
            QSplitter::handle {background:#d2d2d2;}
        """)
    def apply_style_light(self):
        self.current_theme="light";palette=QPalette()
        palette.setColor(QPalette.Window,QColor("#F7F9FA"));palette.setColor(QPalette.WindowText,QColor("#202124"))
        palette.setColor(QPalette.Base,QColor("#FFFFFF"));palette.setColor(QPalette.AlternateBase,QColor("#F0F3F5"))
        palette.setColor(QPalette.Text,QColor("#202124"));palette.setColor(QPalette.Button,QColor("#E8EBF0"))
        palette.setColor(QPalette.ButtonText,QColor("#202124"));palette.setColor(QPalette.Highlight,QColor("#4A73F3"))
        palette.setColor(QPalette.HighlightedText,QColor("#FFFFFF"));self.setPalette(palette)
        self.setStyleSheet("""
            QPushButton {background-color:#4A73F3;color:#ffffff;}
            QPushButton:hover {background-color:#335ee0;}
            QPushButton:pressed {background-color:#284bb9;}
            QTabBar::tab {background:#E1E5EC;color:#1F2225;}
            QTabBar::tab:selected {background:#4A73F3;color:#fff;}
            QLineEdit, QTextEdit, QSpinBox, QComboBox {background:#FFFFFF;color:#202124;}
        """);self.apply_common_styles()
    def apply_style_dark(self):
        self.current_theme="dark";palette=QPalette()
        palette.setColor(QPalette.Window,QColor("#1E2127"));palette.setColor(QPalette.WindowText,QColor("#E6E6E6"))
        palette.setColor(QPalette.Base,QColor("#2B2F36"));palette.setColor(QPalette.AlternateBase,QColor("#323841"))
        palette.setColor(QPalette.Text,QColor("#E0E0E0"));palette.setColor(QPalette.Button,QColor("#3B414B"))
        palette.setColor(QPalette.ButtonText,QColor("#F5F5F5"));palette.setColor(QPalette.Highlight,QColor("#5865F2"))
        palette.setColor(QPalette.HighlightedText,QColor("#000000"));self.setPalette(palette)
        self.setStyleSheet("""
            QPushButton {background-color:#5865F2;color:#ffffff;}
            QPushButton:hover {background-color:#4752c4;}
            QPushButton:pressed {background-color:#3942a1;}
            QTabBar::tab {background:#3b3f46;color:#ddd;}
            QTabBar::tab:selected {background:#5865F2;color:#fff;}
            QLineEdit, QTextEdit, QSpinBox, QComboBox {background:#2e3138;color:#ddd;border:1px solid #555;}
        """);self.apply_common_styles()
if __name__=="__main__":
    app=QApplication(sys.argv);window=CryptoSuite();window.show();sys.exit(app.exec())
