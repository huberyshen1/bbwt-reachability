#!/usr/bin/env python3
"""Check the exact proof details added in the revision; standard library only."""
import itertools,json,hashlib,pathlib
from audit_verify import B,I,rotations
r={'checks':{},'failures':[]}
def check(ok,**data):
 if not ok:r['failures'].append(data)
n=0
for E,C,R in itertools.product(range(1,21),repeat=3):
 if C<R+1:continue
 w='ca'+'b'*(E-1)+'c'*(C-1)+'b'*(R+1)
 F='a'+'b'*(E+R)+'c'*C
 psi=sorted(range(len(w)),key=lambda j:(w[j],j))
 j=E+C # zero-based version of entry e'+e_c+1
 q=0
 while F[j]=='c':
  q+=1;j=psi[j]
 expected=C//(R+1)
 check(q==expected,test='q_formula',E=E,C=C,R=R,q=q,expected=expected)
 if C%(R+1)==0:check(j==0,test='closing',E=E,C=C,R=R)
 else:check(F[j]=='b',test='exit_b',E=E,C=C,R=R)
 n+=1
r['checks']['b3_exact_q_1_to_20']=n
n=0
for A,E,R in itertools.product(range(1,11),repeat=3):
 x='a'*A+'b'*E+'c'+'b'*R;y=B(x);z=I(y[1:]+y[:1])
 expected='a'+'b'*(E+1)+'c'+'b'*(R-1)+'a'*(A-1)
 check(z==expected,test='c_identity',A=A,E=E,R=R,actual=z)
 n+=1
r['checks']['c_exact_identity_1_to_10']=n
n=0
for m in range(1,9):
 for tup in itertools.product('bc',repeat=m):
  u=''.join(tup)
  sentinel=''.join(w[-1] for w in sorted(rotations(u+'$')))
  for A in range(1,5):
   s='a'*A+u
   expected=u[-1]+'a'*(A-1)+sentinel[1:].replace('$','a')
   check(B(s)==expected,test='sentinel',u=u,A=A)
   check(B(u+'a'*A)=='a'*A+B(u),test='inner_B',u=u,A=A)
   check(I(s)==I(u)+'a'*A,test='inner_inverse',u=u,A=A)
   n+=1
r['checks']['sentinel_and_inner_u_length_le_8_e_le_4']=n
r['script_sha256']=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()
pathlib.Path('proof_details_results.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
if r['failures']:raise SystemExit(1)
