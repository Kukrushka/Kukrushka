# Эксперимент: "трудные" простые для гипотезы Эрдёша–Штрауса.
# Ищем 4/p = 1/x + 1/y + 1/z, x = (p+t)/4, t = 4x - p (t ≡ 3 mod 4).
# Остаток t/(p x) = 1/y + 1/z  <=>  (a y - b)(a z - b) = b^2, где a/b = t/(p x) после сокращения.
import sys, json, collections
from math import gcd
from fractions import Fraction as F
N = int(sys.argv[1]) if len(sys.argv) > 1 else 10**6
HARD = {1,121,169,289,361,529}
sieve = bytearray([1])*(N+1); sieve[0]=sieve[1]=0
for i in range(2,int(N**.5)+1):
    if sieve[i]: sieve[i*i::i]=bytearray(len(sieve[i*i::i]))
spf = list(range(N+1))   # наименьший простой делитель, для разложения x
for i in range(2,int(N**.5)+1):
    if spf[i]==i:
        for j in range(i*i,N+1,i):
            if spf[j]==j: spf[j]=i
def factor(n):
    f=collections.Counter()
    while n>1 and n<=N: q=spf[n]; f[q]+=1; n//=q
    if n>1: f[n]+=1
    return f
def divisors(f):
    ds=[1]
    for q,e in f.items(): ds=[d*q**k for d in ds for k in range(e+1)]
    return ds
def try_t(p,t):
    if (p+t)%4: return None
    x=(p+t)//4; a,b=t,p*x; g=gcd(a,b); a//=g; b//=g
    fb=factor(b//p) if b%p==0 else factor(b)
    if b%p==0: fb[p]+=1
    f2=collections.Counter({q:2*e for q,e in fb.items()})
    best=None
    for d in divisors(f2):
        if d<=b and (b+d)%a==0 and (b+b*b//d)%a==0:
            y,z=(b+d)//a,(b+b*b//d)//a
            if best is None or z<best[2]: best=(x,y,z,d)
    return best
hard=[p for p in range(2,N+1) if sieve[p] and p%840 in HARD]
res=[]; tcount=collections.Counter(); worst=[]
for p in hard:
    t=3
    while True:
        s=try_t(p,t)
        if s: break
        t+=4
    x,y,z,d=s
    assert F(1,x)+F(1,y)+F(1,z)==F(4,p)
    typ = "II" if (y%p==0 and z%p==0) else ("I" if (y%p==0)!=(z%p==0) else "0")
    res.append((p,t,x,y,z,typ)); tcount[t]+=1
print(f"Трудных простых до {N}: {len(hard)}; все разложены и проверены дробями: OK")
print("Классы mod 840:", dict(collections.Counter(p%840 for p in hard)))
print("Минимальное t=4x-p, которое сработало (t: сколько простых):")
cum=0
for t in sorted(tcount):
    cum+=tcount[t]
    if t<=31 or tcount[t]: print(f"  t={t:3d}: {tcount[t]:5d}  (накоплено {100*cum/len(hard):5.1f}%)")
print("Тип решения (сколько из y,z делятся на p):", dict(collections.Counter(r[5] for r in res)))
res.sort(key=lambda r:-r[1])
print("Самые 'упрямые' простые (наибольшее t):")
for r in res[:8]: print(f"  p={r[0]}: t={r[1]}, 4/p = 1/{r[2]} + 1/{r[3]} + 1/{r[4]}")
# t=3 работает или нет — зависит ли это только от p mod 840·11·13? проверим, что одного класса недостаточно
by=collections.defaultdict(set)
for r in res: by[r[0]%(840*11)].add(r[1]==3)
mixed=sum(1 for v in by.values() if len(v)==2)
print(f"Классов mod 840·11, где t=3 то работает, то нет: {mixed} из {len(by)}  (=> зависит не только от остатка, как и предсказывает Морделл)")
json.dump(res,open(sys.argv[2],"w")) if len(sys.argv)>2 else None
