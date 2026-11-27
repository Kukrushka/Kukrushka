# Для трудных p ≤ 1e7 и простых t ≡ 3 (mod 4): работает ли x=(p+t)/4, и сравнение с критериями.
import collections, sys
N0=10**7
HARD={1,121,169,289,361,529}
sieve=bytearray([1])*(N0+1); sieve[0]=sieve[1]=0
for i in range(2,int(N0**.5)+1):
    if sieve[i]: sieve[i*i::i]=bytearray(len(sieve[i*i::i]))
spf=list(range(N0//4+200))
for i in range(2,int(len(spf)**.5)+1):
    if spf[i]==i:
        for j in range(i*i,len(spf),i):
            if spf[j]==j: spf[j]=i
def pf(n):
    f=collections.Counter()
    while n>1: r=spf[n]; f[r]+=1; n//=r
    return f
hard=[p for p in range(2,N0+1) if sieve[p] and p%840 in HARD]
for t in (7,11,19,23):
    QR={(k*k)%t for k in range(1,t)}
    cm=collections.Counter(); v2=collections.Counter(); pqr=collections.Counter()
    for p in hard:
        q=(p+t)//4; f=pf(q); fN=f.copy(); fN[p]+=1; N=p*q
        reach={1}
        for r,e in fN.items():
            reach={(a*pow(r,k,t))%t for a in reach for k in range(2*e+1)}
        works=(-N)%t in reach
        Cq=any(r%t not in QR for r in f)            # невычет среди делителей q
        CN=Cq or (p%t not in QR)                     # невычет среди делителей N (вкл. p)
        cm[(CN,works)]+=1; pqr[p%t in QR]+=1
        if CN and not works: v2[f[2]]+=1
    n=len(hard); w=sum(v for (c,wk),v in cm.items() if wk)
    print(f"t={t}: работает {w}/{n} = {100*w/n:.1f}%;  p — вычет mod t: {pqr[True]}, невычет: {pqr[False]}")
    print(f"   [есть невычет у N, работает]: да,да={cm[(True,True)]}  да,нет={cm[(True,False)]}  нет,да={cm[(False,True)]}  нет,нет={cm[(False,False)]}")
    if v2: print(f"   провалы при наличии невычета — распределение v2(q): {dict(sorted(v2.items()))}")
