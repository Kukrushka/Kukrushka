import collections
from math import gcd
from fractions import Fraction as F
N0=10**7
HARD={1,121,169,289,361,529}
sieve=bytearray([1])*(N0+1); sieve[0]=sieve[1]=0
for i in range(2,int(N0**.5)+1):
    if sieve[i]: sieve[i*i::i]=bytearray(len(sieve[i*i::i]))
def pf(n):
    f=collections.Counter();d=2
    while d*d<=n:
        while n%d==0: f[d]+=1;n//=d
        d+=1
    if n>1: f[n]+=1
    return f
def t7(p):
    q=(p+7)//4; N=p*q; f=pf(q); f[p]+=1
    reach={1}
    for r,e in f.items():
        reach={(a*pow(r,k,7))%7 for a in reach for k in range(2*e+1)}
    return ((-N)%7 in reach), f
# 1) утверждения системы на любых простых p≡1 mod 4 (не только трудных)
for p in (17,41,421,1009,2437,673):
    print(p,'mod840=',p%840,'трудное' if p%840 in HARD else 'НЕ трудное','p mod7=',p%7,'t=7:',t7(p)[0])
cls=collections.Counter(); ok=collections.Counter(); allp=collections.Counter(); allok=collections.Counter()
qnr_ok=collections.Counter()
for p in range(5,N0+1,4):
    if not sieve[p]: continue
    w,f=t7(p); m=p%7; allp[m]+=1; allok[m]+=w
    if p%840 in HARD:
        cls[m]+=1; ok[m]+=w
        hasqnr=any(r%7 in (3,5,6) for r in f if r!=p)
        qnr_ok[(hasqnr,w)]+=1
print('\nВсе простые p≡1 mod 4 до 1e7: доля, где t=7 работает, по p mod 7:')
for m in sorted(allp): print(f'  p≡{m}: {allok[m]}/{allp[m]} = {100*allok[m]/allp[m]:.1f}%')
print('\nТРУДНЫЕ простые до 1e7, по p mod 7:')
for m in sorted(cls): print(f'  p≡{m}: {ok[m]}/{cls[m]} = {100*ok[m]/cls[m]:.1f}%')
print('\nТрудные: (у q есть простой делитель-невычет mod 7, t=7 работает) -> количество:', dict(qnr_ok))
