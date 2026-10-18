"""Exact symbolic checks for the qutrit channel and PPT activation partner.

Matrix identities are evaluated exactly. Entropy and capacity theorems are
verified separately by Lean. Any failed certificate exits nonzero.
"""
from itertools import product
import sympy as s

R, I = s.Rational, s.I
sqrt, eye, zeros, Matrix, kron = s.sqrt, s.eye, s.zeros, s.Matrix, s.kronecker_product
checks = 0

def check(name, condition):
    global checks
    if not bool(condition):
        raise AssertionError(name)
    checks += 1
    print('PASS', name, flush=True)

def eq(A, B):
    if hasattr(A, 'shape'):
        return all(s.simplify(x) == 0 for x in A - B)
    return s.simplify(A-B) == 0

def unit(n, i, j):
    M = zeros(n); M[i, j] = 1
    return M

def vec(M):
    return Matrix(list(M))  # row-major: |j><k| maps to |j>|k|

A = [Matrix(3, 3, lambda j, k: s.LeviCivita(mu, j, k)) for mu in range(3)]
K = [eye(3)/sqrt(2)] + [a/2 for a in A]

def lam(X):
    return X/2 + (s.trace(X)*eye(3)-X.T)/4

def comp(X):
    return Matrix(4, 4, lambda a, b: s.trace(K[a]*X*K[b].H))

def shadow(Y):
    a = Matrix([Y[1, 2]-Y[2, 1], Y[2, 0]-Y[0, 2], Y[0, 1]-Y[1, 0]])
    return Matrix.vstack(Matrix.hstack(Matrix([[s.trace(Y)/3]]), sqrt(2)*a.T/3),
                         Matrix.hstack(-sqrt(2)*a/3, (2*s.trace(Y)*eye(3)-Y-2*Y.T)/3))

X = Matrix(3, 3, s.symbols('x:9'))
check('Lambda Kraus formula', eq(lam(X), sum((k*X*k.H for k in K), zeros(3))))
check('Kraus trace preservation', eq(sum((k.H*k for k in K), zeros(3)), eye(3)))
G = [Matrix(9, 3, lambda jk, i: int(jk//3 == i and jk%3 == mu)
     + R(1,2)*int(jk//3 == mu and jk%3 == i)
     - R(1,2)*int(mu == i and jk//3 == jk%3)) for mu in range(3)]
J = Matrix.hstack(*(vec(shadow(unit(3,j,k))) for j,k in product(range(3),repeat=2)))
check('reconstruction J^dag Lambda^c = Lambda', eq(J.H*vec(comp(X)), vec(lam(X))))
check('adjoint preservation', eq(shadow(X.H), shadow(X).H))
check('nonpositive shadow estimator', eq(shadow(unit(3,0,0)), s.diag(1,-1,2,2)/3))
defect = kron(lam(X), eye(3)) - J.H*kron(comp(X), eye(4))*J
check('actual outer defect = exact Kraus expression',
      eq(defect, R(2,9)*sum((g*X*g.H for g in G), zeros(9))))
check('Tr(G_mu^dag G_nu) = 4 delta_mu,nu', all(
    eq(s.trace(G[mu].H*G[nu]), 4*int(mu==nu)) for mu,nu in product(range(3),repeat=2)))

Phi = vec(eye(3))*vec(eye(3)).H/3
F = Matrix(9,9,lambda i,j:int(i//3==j%3 and i%3==j//3))
omega = Phi/2+(eye(9)-F)/12
actual_choi = Matrix(9,9,lambda i,j:lam(unit(3,i//3,j//3))[i%3,j%3])/3
check('normalized Choi of actual Lambda', eq(omega,actual_choi))
pt = Matrix(9,9,lambda i,j:omega[3*(j//3)+i%3,3*(i//3)+j%3])
check('Choi partial transpose identity', eq(pt,(eye(9)+2*F-3*Phi)/12))
check('complete NPT spectrum',pt.eigenvals()=={R(1,4):5,s.Integer(0):1,R(-1,12):3})
v = zeros(9,1);v[1]=1/sqrt(2);v[3]=-1/sqrt(2)
check('Schmidt-rank-two normalized witness',eq((v.H*pt*v)[0],R(-1,12)))
check('basis outputs used in non-antidegradability proof',all(
    eq(lam(unit(3,i,i)),(eye(3)+unit(3,i,i))/4) and
    eq(comp(unit(3,i,i)),unit(4,0,0)/2+sum((unit(4,j+1,j+1) for j in range(3) if j!=i),zeros(4))/4)
    for i in range(3)))

g=Matrix([1,I,0])/sqrt(2); k=s.conjugate(g); e2=Matrix([0,0,1])
V=Matrix.hstack(g,e2)
R0=Matrix.vstack(e2.H,-k.H);R1=Matrix.vstack(g.H,zeros(1,3))
def C(X):
    out=lam(V*X*V.H)
    return R0*out*R0.H+R1*out*R1.H
check('qubit encoder isometry and decoder TP',eq(V.H*V,eye(2)) and eq(R0.H*R0+R1.H*R1,eye(3)))
expected=[unit(2,0,0),unit(2,0,1)/4,unit(2,1,0)/4,3*unit(2,0,0)/4+unit(2,1,1)/4]
check('all four qubit matrix units',all(eq(C(unit(2,i,j)),expected[2*i+j]) for i,j in product(range(2),repeat=2)))
for d in (1,2,3,4):
    # Check the tensor action directly, without constructing a Kraus list of size 2^d.
    for i,j in product(range(d),repeat=2):
        factors=[C(unit(2,int(t==i),int(t==j))) for t in range(d)]
        out=kron(*factors) if d>1 else factors[0]
        target=(unit(2**d,2**(d-i-1),2**(d-j-1))/16 if i!=j else
                unit(2**d,2**(d-i-1),2**(d-i-1))/4+3*unit(2**d,0,0)/4)
        check(f'single excitation d={d}, i={i}, j={j}',eq(out,target))

beta=[Matrix(x)/sqrt(2) for x in ([1,0,0,1],[1,0,0,-1],[0,1,1,0],[0,1,-1,0])]
chi=[Matrix([sqrt(2+sqrt(2)),0,0,sqrt(2-sqrt(2))])/2,
     Matrix([sqrt(2-sqrt(2)),0,0,-sqrt(2+sqrt(2))])/2]
tau=[(unit(4,0,0)+beta[2]*beta[2].H)/2,(unit(4,3,3)+beta[3]*beta[3].H)/2,
     chi[0]*chi[0].H,chi[1]*chi[1].H]
tau=[m.applyfunc(s.simplify) for m in tau]
q=2-sqrt(2)
O=sum(((q if j<2 else 1-q)/2*kron(beta[j]*beta[j].H,tau[j]) for j in range(4)),zeros(16))
O=O.applyfunc(s.simplify)
def regroup_index(i):
    a,ap,b,bp=(i//8,(i//4)%2,(i//2)%2,i%2)
    return 8*a+4*b+2*ap+bp
perm=[regroup_index(i) for i in range(16)]
Or=O.extract(perm,perm)
ptr=Matrix(16,16,lambda i,j:Or[4*(i//4)+j%4,4*(j//4)+i%4])
check('helper invariant under full BBprime transpose',eq(ptr,Or))
marg=Matrix(4,4,lambda i,j:sum(Or[4*i+b,4*j+b] for b in range(4)))
check('helper Choi marginal',eq(marg,eye(4)/4))
check('shield trace and orthogonality',all(eq(s.trace(t),1) for t in tau) and eq(tau[0]*tau[1],zeros(4)) and eq(tau[2]*tau[3],zeros(4)))
support_vecs=[kron(beta[0],Matrix([1,0,0,0])),kron(beta[0],beta[2]),
              kron(beta[1],Matrix([0,0,0,1])),kron(beta[1],beta[3]),
              kron(beta[2],chi[0]),kron(beta[3],chi[1])]
U=Matrix.hstack(*(v.extract(perm,[0]) for v in support_vecs))
lambdas=[q/4]*4+[(1-q)/2]*2
check('six orthonormal support eigenvectors',eq(U.H*U,eye(6)))
check('exact PSD spectral certificate',eq(Or,U*s.diag(*lambdas)*U.H) and all(v>0 for v in lambdas))
Z=kron(s.diag(1,-1),eye(2))
check('environment independence via support compression',eq(U.H*kron(Z,eye(4))*U,zeros(6)))
KH=[2*sqrt(lambdas[l])*Matrix(4,4,list(U[:,l])).T for l in range(6)]
check('full complementary Kraus orientation and TP',eq(sum((k.H*k for k in KH),zeros(4)),eye(4)))
for x in range(2):
    rho=kron(unit(2,x,x),eye(2)/2)
    receiver=sum((k*rho*k.H for k in KH),zeros(4))
    expected=kron(q*unit(2,x,x)+(1-q)*unit(2,1-x,1-x),eye(2)/2)
    environment=Matrix(6,6,lambda l,m:s.trace(KH[l]*rho*KH[m].H))
    check(f'helper receiver x={x}',eq(receiver,expected))
    check(f'FULL helper environment x={x}',eq(environment,s.diag(*lambdas)))
print('Private-information expression (numeric display only):',
      s.N(1+q*s.log(q,2)+(1-q)*s.log(1-q,2),25))
print(f'Completed {checks} exact checks. Entropy/capacity proofs are verified separately in Lean.')
