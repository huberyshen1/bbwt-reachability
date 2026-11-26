#!/usr/bin/env python3
"""Independent bounded audit. Standard library only; not the authors' software.
Run: python3 audit_verify.py --out audit_results.json
Indices in generated permutations/certificates are zero-based.
"""
import argparse, collections, functools, hashlib, itertools, json, math, pathlib, platform, random, time

def rotations(s):
    return [s[i:] + s[:i] for i in range(len(s))]

def necklace(s):
    return min(rotations(s))

def duval(s):
    i = 0
    out = []
    while i < len(s):
        j, k = i + 1, i
        while j < len(s) and s[k] <= s[j]:
            k = i if s[k] < s[j] else k + 1
            j += 1
        step = j - k
        while i <= k:
            out.append(s[i:i+step])
            i += step
    return out

def omega_cmp(u, v):
    return (u+v > v+u) - (u+v < v+u)

@functools.lru_cache(maxsize=200000)
def B(s):
    rows = [r for f in duval(s) for r in rotations(f)]
    rows.sort(key=functools.cmp_to_key(omega_cmp))
    return ''.join(r[-1] for r in rows)

@functools.lru_cache(maxsize=200000)
def I(t):
    # Stable sorted positions implement F-index -> L-index, independently of B.
    psi = sorted(range(len(t)), key=lambda j: (t[j], j))
    F = ''.join(sorted(t))
    seen, words = set(), []
    for j in range(len(t)):
        if j in seen:
            continue
        w, k = '', j
        while k not in seen:
            seen.add(k)
            w += F[k]
            k = psi[k]
        words.append(w)
    assert words == sorted(words)
    return ''.join(reversed(words))

def multinomial(p):
    n, m = 0, 1
    for c in p:
        m *= math.comb(n+c, c)
        n += c
    return m

def vectors(sigma, cap):
    def rec(prefix, lower):
        if len(prefix) == sigma:
            yield from sorted(set(itertools.permutations(prefix)))
            return
        c = lower
        while multinomial(prefix + [c]*(sigma-len(prefix))) <= cap:
            yield from rec(prefix+[c], c)
            c += 1
    return sorted(rec([], 1))

def words(p):
    alphabet = 'abcde'[:len(p)]
    counts = list(p)
    n = sum(p)
    def rec(pre):
        if len(pre) == n:
            yield pre
            return
        for j, c in enumerate(counts):
            if c:
                counts[j] -= 1
                yield from rec(pre+alphabet[j])
                counts[j] += 1
    return list(rec(''))

def obstruction_words(maxn):
    # Exactly one run containing all a's, then a positive b-run, then c, ends b.
    for n in range(4, maxn+1):
        for A in range(1, n-2):
            for tail in itertools.product('bc', repeat=n-A-2):
                u = 'b'+''.join(tail)+'b'
                if 'c' in u:
                    yield 'a'*A+u

def branch(x):
    A = len(x)-len(x.lstrip('a'))
    tail = x[A:]
    E = len(tail)-len(tail.lstrip('b'))
    R = len(x)-len(x.rstrip('b'))
    C = x.count('c')
    if A == 1:
        if E+R < x.count('b'):
            m = x.rfind('c')
            return 'b1', I(x[m:]+x[:m])
        if C == 1:
            return 'b2', B(x)
        w = B(x)
        return 'b3', I(w[R:]+w[:R])
    if C == 1:
        w = B(x)
        return 'c', I(w[1:]+w[:1])
    return None, None

def eccentricity(perms):
    n = len(perms[0])
    ds = [-1]*n
    ds[0] = 0
    todo = collections.deque([0])
    while todo:
        i = todo.popleft()
        for p in perms:
            j = p[i]
            if ds[j] < 0:
                ds[j] = ds[i]+1
                todo.append(j)
    return max(ds), sum(d >= 0 for d in ds)

def inverse(p):
    q = [0]*len(p)
    for i,j in enumerate(p): q[j] = i
    return q

def cycles(p):
    seen, out = set(), []
    for i in range(len(p)):
        if i not in seen:
            c, j = [], i
            while j not in seen:
                seen.add(j); c.append(j); j = p[j]
            out.append(c)
    return out

def minimal_congruence(gens, j):
    n = len(gens[0]); parent = list(range(n)); sz = [1]*n
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    todo = [(0,j)]
    while todo:
        a,b = map(find, todo.pop())
        if a == b: continue
        if sz[a] < sz[b]: a,b = b,a
        parent[b] = a; sz[a] += sz[b]
        todo.extend((g[a],g[b]) for g in gens)
    return [find(i) for i in range(n)]

def jordan(gens, rng):
    n = len(gens[0]); p = list(range(n)); word = []
    choices = [gens[0], gens[1], inverse(gens[0]), inverse(gens[1])]
    for step in range(1, 20001):
        k = rng.randrange(4); word.append(k)
        p = [choices[k][v] for v in p]
        cs = cycles(p); sizes = [len(c) for c in cs]
        for q in set(sizes):
            if q < 2 or q > n-3 or any(q%d == 0 for d in range(2,math.isqrt(q)+1)):
                continue
            if sizes.count(q) != 1 or any(z%q == 0 for z in sizes if z != q):
                continue
            power = math.lcm(*(z for z in sizes if z != q))
            # Applying the word then powering isolates one q-cycle.
            powered = [i for i in range(n)]
            for c in cs:
                for j,v in enumerate(c): powered[v] = c[(j+power)%len(c)]
            assert sorted(len(c) for c in cycles(powered) if len(c)>1) == [q]
            return {'word':word, 'prime':q, 'power':power, 'cycle_lengths':sizes}
    return None

def main(out):
    start = time.time()
    result = {'scope':'Independent audit, not a rerun of the unavailable C++ project',
              'python':platform.python_version(), 'platform':platform.platform(),
              'seed':20261125, 'failures':[]}
    def check(ok, **data):
        if not ok: result['failures'].append(data)
    result['roundtrip'] = {}
    for alphabet in ['abc','abcd']:
        total = 0
        for n in range(1,7):
            for tup in itertools.product(alphabet, repeat=n):
                s = ''.join(tup); total += 1
                check(I(B(s)) == s and B(I(s)) == s, test='roundtrip',s=s)
        result['roundtrip'][alphabet] = total
    print('roundtrip done', flush=True)
    result['scope_statistics'] = {}
    for sigma in [3,4,5]:
        ps = vectors(sigma, 200000)
        result['scope_statistics'][sigma] = {
            'vectors':len(ps), 'states':sum(map(multinomial,ps)),
            'n_max':max(map(sum,ps)), 'max_N':max(map(multinomial,ps)),
            'vectors_N_le_2000':sum(multinomial(p)<=2000 for p in ps)}
    result['four_run'] = 0
    for A,E,C,R in itertools.product(range(1,9),repeat=4):
        x = 'a'*A+'b'*E+'c'*C+'b'*R
        rhs = 'b'+'a'*(A-1)+'b'*(R-1)+'c'+'a'+'b'*(E-1)+'c'*(C-1)+'b'
        check(B(x)==rhs,test='four_run',x=x,actual=B(x),expected=rhs)
        result['four_run'] += 1
    counts = collections.Counter()
    for x in obstruction_words(15):
        name,z = branch(x)
        if name:
            counts[name] += 1
            check(necklace(z)<x,test=name,x=x,z=z)
    result['constructive_branches_n_le_15'] = dict(counts)
    print('constructive branches done', dict(counts), flush=True)
    result['two_step_n_le_13'] = {'total':0,'one':0,'two':0,'by_n':{}}
    for x in obstruction_words(13):
        result['two_step_n_le_13']['total'] += 1
        byn = result['two_step_n_le_13']['by_n']
        byn[len(x)] = byn.get(len(x),0)+1
        one = {necklace(f(r)) for r in rotations(x) for f in [B,I]}
        if min(one) < x:
            result['two_step_n_le_13']['one'] += 1; continue
        found = any(necklace(f(r)) < x for y in one for r in rotations(y) for f in [B,I])
        result['two_step_n_le_13']['two'] += int(found)
        check(found,test='two_step',x=x)
    print('two-step done', result['two_step_n_le_13'], flush=True)
    result['theorem4a'] = 0
    for k in range(1,21):
        n=k+2
        for a in range(n):
            for c in range(n):
                if a==c: continue
                w=list('b'*n); w[a]='a'; w[c]='c'; w=''.join(w)
                check(B(w).index('c')==n-1-c,test='4a',w=w)
                result['theorem4a'] += 1
    result['theorem4b'] = {'per_sigma':{}}
    for sigma in [3,4,5]:
        count = 0
        for p in vectors(sigma,2000):
            if p[:2] != (1,1): continue
            for w in words(p):
                merge=lambda s:s.replace('b','a')
                check(merge(B(w))==B(merge(w)) and merge(I(w))==I(merge(w)),test='4b',w=w)
                count += 1
        result['theorem4b']['per_sigma'][sigma] = count
    result['sentinel_example'] = {
        'u':'bcbb','sentinel_BWT':''.join(r[-1] for r in sorted(rotations('bcbb$'))),
        'B_s':B('aaabcbb'),'B_rot3_s':B('bcbbaaa'),
        'I_s':I('aaabcbb'),'B_u':B('bcbb'),'I_u':I('bcbb')}
    print('structural theorems done',flush=True)
    result['groups'] = []
    rng = random.Random(result['seed'])
    for p in vectors(3,500):
        ws = words(p); index={w:i for i,w in enumerate(ws)}
        gens = [[index[B(w)] for w in ws],[index[w[1:]+w[:1]] for w in ws]]
        n=len(ws); fwd, reached = eccentricity(gens)
        sym,_ = eccentricity(gens+[inverse(g) for g in gens])
        check(reached==n,test='transitivity_small',p=p,reached=reached)
        parity = [(n-len(cycles(g)))%2 for g in gens]
        closures=[]; block=None
        for j in range(1,n):
            labels = minimal_congruence(gens,j)
            size = sum(x==labels[0] for x in labels)
            if size < n:
                block = [[i for i in range(n) if labels[i]==v] for v in sorted(set(labels))]
                break
            closures.append(size)
        row={'p':p,'N':n,'fwd':fwd,'sym':sym,'parity':parity}
        if block:
            row.update(classification='imprimitive',blocks=block)
        else:
            cert = jordan(gens,rng)
            row.update(classification=('S' if any(parity) else 'A') if cert else 'uncertified_primitive',
                       primitive_closure_sizes=closures,jordan=cert)
        result['groups'].append(row)
    result['group_counts'] = dict(collections.Counter(r['classification'] for r in result['groups']))
    print('groups done',result['group_counts'],flush=True)
    result['p_1_98_1'] = {}
    # No full-length rotation sorting: this exact family formula follows from
    # Theorem 4(a)'s inverse expression and is cross-checked with I for k<=20.
    def family_I(t):
        n=len(t); q=t.index('a')+1; r=t.index('c')+1
        if q<r:return 'b'*(n-r)+'c'+'b'*(r-q-1)+'a'+'b'*(q-1)
        return 'b'*(q-r-1)+'a'+'b'*(n-q)+'c'+'b'*(r-1)
    for k in range(1,21):
        for w in words((1,k,1)):
            check(family_I(w)==I(w),test='family_inverse',w=w)
    ws=words((1,98,1)); index={w:i for i,w in enumerate(ws)}
    bi=[index[family_I(w)] for w in ws]; bg=inverse(bi)
    rg=[index[w[1:]+w[:1]] for w in ws]
    result['p_1_98_1']['fwd'],result['p_1_98_1']['reached']=eccentricity([bg,rg])
    result['p_1_98_1']['sym'],_=eccentricity([bg,rg,bi,inverse(rg)])
    n=100
    qr=[(j-1)%n for j in range(n)]; qb=[n-1-j for j in range(n)]
    # Reindex quotient BFS to start at c-position n-1 of sorted word.
    def quotient_ecc(perms):
        shifted=[[ (g[(j+n-1)%n]-(n-1))%n for j in range(n)] for g in perms]
        return eccentricity(shifted)[0]
    result['p_1_98_1']['quotient_fwd']=quotient_ecc([qb,qr])
    result['p_1_98_1']['quotient_sym']=quotient_ecc([qb,qr,inverse(qr)])
    result['seconds']=round(time.time()-start,3)
    result['script_sha256']=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()
    pathlib.Path(out).write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['groups','failures']},ensure_ascii=False,indent=2))
    print('failures',len(result['failures']))
    if result['failures']: raise SystemExit(1)

if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--out',default='audit_results.json')
    args=ap.parse_args(); main(args.out)
