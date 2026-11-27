import collections
exec(open('tgen.py').read().split("for t in (7,11,19,23):")[0])
t=23; QR={(k*k)%t for k in range(1,t)}
stats=collections.Counter(); shapes=collections.Counter(); ex=[]
allv2=collections.Counter(); failv2=collections.Counter()
for p in hard:
    q=(p+t)//4; f=pf(q); fN=f.copy(); fN[p]+=1; N=p*q
    reach={1}
    for r,e in fN.items(): reach={(a*pow(r,k,t))%t for a in reach for k in range(2*e+1)}
    works=(-N)%t in reach
    nqr=[(r,e) for r,e in fN.items() if r%t not in QR]
    if nqr: allv2[f[2]]+=1
    if nqr and not works:
        failv2[f[2]]+=1
        stats['p вычет' if p%t in QR else 'p невычет']+=1
        shapes[(len(nqr), tuple(sorted(e for _,e in nqr)), len(fN)-len(nqr)-1)]+=1  # (#невычетов, кратности, #вычетных простых кроме 2)
        if len(ex)<5: ex.append((p,dict(f)))
print("p в провалах:",dict(stats))
print("форма провалов (число невычетных простых, их кратности, число прочих простых кроме 2):",shapes.most_common(8))
print("v2(q) среди всех p с невычетом:",dict(sorted(allv2.items())),"  среди провалов:",dict(failv2))
print("примеры:",ex)
