###
# Security estimates of LWE and SIS from [LNP22] available at https://eprint.iacr.org/2022/284.pdf
###

from MSIS_security import SIS_optimize_attack, SIS_l2_cost, SIS_linf_cost
from MLWE_security import MLWE_optimize_attack, LWE_primal_cost, LWE_dual_cost
from model_BKZ import svp_classical
from math import sqrt, floor, ceil, log, exp
from sympy import nextprime
from estimator_ntru import combined_attack_prob
from one_more_sis_security import combinatorial, lattice_attack

pi = 3.1415926535897932384626433832795028841971693993751058209749


Kilo = 1024
G_entropy_const = 4.13
#4.13 as in 2022/141
#[LNP22] uses 24


###############################################################################
#
# variables that define LWE/SIS hardness differ in [LNP22] from Fig.10 to Fig.6
# below is the transition dictionary.
# We instantiate Fig.10, monitor how the parameters get updated to Fig.6
# and instantiate Thm. 4.2. with the updated parameters. The result is given
# in the HARDNESS section below.
#
#               |  Fig.10    |    Fig.8                 | Fig.6
# ______________________________________________________________________________
#   A1.nrows    |   n        |    n                     |    n
#   s1.dim      |   m1       |    m1+ve                 |  m1+ve
#   s2.dim      |   m2       |    m2                    |    m2
#   m.dim       |   ell      |    ell+(256/d+1)*{0,1,2} | Fig.8+lamb/2
# ______________________________________________________________________________
#                               HARDNESS (Thm. 4.2)
#                       here m1 and ell are those of Fig.10
#   LWE:        |
#      dim      |   m2-n-ell-{0,1,2}*(256/d+1)-lamb/2-1
#      Nsamples |   n+ell+{0,1,2}*(256/d+1)+lamb/2+1
# ______________________________________________________________________________
#   SIS:
#    hight of A |   n
#    width of A |   m1+m2+ve
#
#
#   multiplication by a set in m.dim for Fig.8 and hardness must be
#   understood as follows:  we multiply
#       by 0 if ve=vd=0,
#       by 1 if only one of {ve,vd} is at least 1,
#       by 2 if both {ve,vd} are at least 1
#
#
############################################################################

def SIS_security(paramset):
    # as per [LNP22] Thm 4.2 (see above dictionary)
    d  = paramset['d']
    q  = paramset['q']
    n  = paramset['n']
    m1 = paramset['m1']
    m2 = paramset['m2']
    norm_s1  = paramset['norm_s1']
    ve = paramset['ve']
    nu = paramset['nu']
    eta    = paramset['eta']
    gamma1 = paramset['gamma1']
    gamma2 = paramset['gamma2']
    D  = paramset['D']
    sigma1 = gamma1*eta*sqrt(norm_s1+ve*d)
    # sqrt(B/2+ve*d)is an upper bound on the ell2-norm of ABDLOP's s1.
    sigma2 = gamma2*eta*sqrt(m2*d*nu)
    # sqrt(m2*nu*d) is an upper bound on the ell2-norm of ABDLOP's s2.
    BSIS = 8*eta*sqrt(sigma1**2*2*m1*d+2*sigma2**2*m2*d)+eta*2**(D-1)*sqrt(n*d)
    assert(BSIS<q)
    max_w = (m1+m2+ve)*d # maximal width
    h = n*d
    ##
    # estimation for the SIS problem A*x = 0 mod q, where A is from Zq^(h X max_w) and ||x||_2 < BSIS
    # returns optimal m, beta, bit complexity
    m_pc, b_pc, c_pc = SIS_optimize_attack(q, max_w, h, BSIS, cost_attack=SIS_l2_cost, cost_svp=svp_classical, verbose=False)
    return (m_pc, b_pc, c_pc)


def LWE_security(paramset, attack=LWE_primal_cost):
    # as per [LNP22] Thm 4.2 (see above dictionary)
    d  = paramset['d']
    q  = paramset['q']
    n  = paramset['n']
    m1 = paramset['m1']
    m2 = paramset['m2']
    nu = paramset['nu']
    ve = paramset['ve']
    vd = paramset['vd']
    ell = paramset['ell']
    lamb = paramset['lambda']
    assert(lamb%2 == 0)
    if vd==0 and ve==0:
        scalar = 0
    elif vd>=1 and ve>=1:
        scalar = 2
    else: scalar = 1
    ell_updated = ell+(round(256/d)+1)*scalar+round(lamb/2)
    mLWE = (n+ell_updated+1)*d
    nLWE = (m2-n-ell_updated-1)*d
    ##
    # estimation for the LWE problem
    # returns optimal m, beta, bit complexity
    m_pc_, b_pc_, c_pc_ = MLWE_optimize_attack(q, nLWE, mLWE, nu, cost_attack=attack, cost_svp=svp_classical, verbose=False)
    return(m_pc_, b_pc_, c_pc_)


def proof_size(paramset):
    d  = paramset['d']
    q  = paramset['q']
    n  = paramset['n']
    m1 = paramset['m1']
    m2 = paramset['m2']
    assert(m1>=512/d)
    assert(m2>=512/d)      # as per Thm 4.3
    alphae  = paramset['alphae']
    norm_s1 = paramset['norm_s1']
    ell = paramset['ell']
    lamb   = paramset['lambda']
    assert(lamb%2 == 0)    # as per Section 4.4
    ve = paramset['ve']
    vd = paramset['vd']
    if vd==0 and ve==0:
        scalar = 0
    elif vd>=1 and ve>=1:
        scalar = 2
    else: scalar = 1
    ell_updated = ell+(round(256/d)+1)*scalar
    #print('ell_updated:',ell_updated)
    ##
    D  = paramset['D']
    nu = paramset['nu']
    eta    = paramset['eta']
    gamma1 = paramset['gamma1']
    gamma2 = paramset['gamma2']
    gammae = paramset['gammae']
    sigma1 = gamma1*eta*sqrt(norm_s1+ve*d) # norm_s1 is the squared norm of ABDLOP's s1 as per Thm. 5.3 (Fig. 10), hence add ve*d (norm of x)
    sigma2 = gamma2*eta*sqrt(nu*m2*d)
    sigma2_trunc = gamma2*eta*sqrt(nu*(m2-n)*d)
    # See [LNP22] footnote 20 (Bai-Galbraith optimization)
    sigmae =gammae*sqrt(337)*(sqrt(alphae+ve*d))
    # See [LNP22] fig 10; this is an upper bound on the norm of s^(e). Note that the bound in "public information" is flawed (misplaced square roots)
    print('proof-size sigmas:', log(G_entropy_const*sigma1, 2), log(G_entropy_const*sigma2, 2), log(G_entropy_const*sigmae, 2))
    lgq             = log(q,2)
    size_plain      = (n+ell+lamb+1)*d*lgq + m1*d*(log(G_entropy_const*sigma1, 2)) + m2*d*(log(G_entropy_const*sigma2,2))+ve*d*(log(G_entropy_const*sigmae,2))
    size_BG         = (n+ell+lamb+1)*d*lgq + m1*d*(log(G_entropy_const*sigma1, 2)) + (m2-n)*d*(log(G_entropy_const*sigma2_trunc,2))+ve*d*(log(G_entropy_const*sigmae,2))
    ##
    # instead of sending full t_A = t_A0+2^D*t_A1, we only send the high order bits t_A1
    # As in Dilithium (https://eprint.iacr.org/2017/633.pdf) we send the carry bits that appear by not adding c*t_A0
    # The prover runs MakeHint(-c*t_A0, w+c*t_A0, |c*t_A0|_oo)
    challnge_size = ceil(log(2*kappa+1,2))*d
    hint_size = n*d #we truncate only t_A as opposed to [LNP22]
    size_cut_tA   = n*d*(lgq-D) + (ell+lamb+1)*d*lgq+ m1*d*(log(G_entropy_const*sigma1, 2)) + m2*d*(log(G_entropy_const*sigma2_trunc,2))+ve*d*(log(G_entropy_const*sigmae,2))
    size_cut_tA   = size_cut_tA + challnge_size + hint_size
    size_BG_cut_tA   = n*d*(lgq-D) + (ell+lamb+1)*d*lgq+ m1*d*(log(G_entropy_const*sigma1, 2)) + (m2-n)*d*(log(G_entropy_const*sigma2_trunc,2))+ve*d*(log(G_entropy_const*sigmae,2))
    size_BG_cut_tA   = size_BG_cut_tA + challnge_size + hint_size
    return (size_plain/(8.*Kilo), size_BG/(8.*Kilo), size_cut_tA/(8.*Kilo), size_BG_cut_tA/(8.*Kilo))





#####################
# Falcon parameters
# Adapted from 1st parameter set of the Falcon NIST submission
# Available at: https://falcon-sign.info/falcon.pdf
#####################
d   = 128
sec = 128
n_F = 512
q_s = 12301
# This is not exactly the one chosen in the Falcon NIST submission, as we need x^128+1 to have only two factors mod q_s
# Note that this is almost the same modulus, implying that there is negligible security impact.
# Maple code: qs := 12301: d:=128: l := numelems((Factors(x^d + 1) mod qs)[2]): isprime(qs), l;
# Maple answer is "true, 2"

epsinv = sqrt(sec*2**64)# R\'enyi divergence stuff, see above (2.13) in Falcon doc
#epsinv = 2**sec # stat. distance
sigma_F = (1/pi)*sqrt(log(4*n_F*(1+epsinv))/2)*1.17*sqrt(q_s)
print('sigma_F:', sigma_F)
# (2.13) in Falcon doc
beta = sigma_F*1.1*sqrt(2*n_F)
# (2.14) in Falcon doc, l2-norm of the signature
beta_inf = ceil(sigma_F*4.2) # FALCON's estimations use 1.1 instead of 4.2
# l2-inf norm bound of the sig, see [Le. 2.2, LNP22] with md=1.
# Probability that a signature has the appropriate norm
# Maple code: t := 4.2: n:=512: (1-t*exp((-t^2 + 1)/2))^(2*n);
# Maple answer is 0.35

print('beta_inf:', beta_inf)
print('beta:', beta)

#Falcon's hardness (use the NTRU hardness estimator)
sigma_fg = 1.17*sqrt(q_s/(2*n_F)) # see Alg.5 in https://falcon-sign.info/falcon.pdf
print('sigma_fg:', sigma_fg)
beta_ntru_skr = combined_attack_prob(q_s, n_F, sigma_fg, "circulant", 8, "SKR", verbose=False)
print(beta_ntru_skr[0], beta_ntru_skr[1])
print('Falcons secret key security as NTRU:', svp_classical(beta_ntru_skr[1]))

signature_key_primal = MLWE_optimize_attack(q_s, n_F, n_F, sigma_fg, cost_attack=LWE_primal_cost, cost_svp=svp_classical, verbose=False)
print('Falcons secret key security as LWE:', signature_key_primal)

#forgery_primal = SIS_optimize_attack(q_s, 2*n_F, n_F, beta_inf, cost_attack=SIS_linf_cost, cost_svp=svp_classical, verbose=False)
#print('Falcons forgery as SIS in ell_infinity:', forgery_primal)

# returns 0 bits of security when beta>q_s
forgery_primal_ell2 = SIS_optimize_attack(q_s, 2*n_F, n_F, beta, cost_attack=SIS_l2_cost, cost_svp=svp_classical, verbose=False)
print('Falcons forgery as SIS in ell_2:', forgery_primal_ell2)


#####################
# Module-LWE security for h'*x1+x2
# (replace the stat. arguments of LHL to computational LWE)
# h' is of the same dimension as Falcon's h
# and we keep the same q
# what we can play with is the size of x1, x2
#####################
tau_x = 2 #ell_oo norm of x1, x2
hprime_lwe_hardness = MLWE_optimize_attack(q_s, n_F, n_F, tau_x, cost_attack=LWE_primal_cost, cost_svp=svp_classical, verbose=False)
print('LWE hardness for hprime:', hprime_lwe_hardness)



#####################
# Encryption Parameters
#
# Use Module-LWE (Kyber) over Rq = Zq[x]/(x^128+1)
# we encrypt:
# -- s1 (the first part of Falcon's signature)
# -- x1, x2 (user's randomizers)
# We have 3 elements over Zq[x]/(x^512+1) to encrypt
#
# a1 \in Rq^{8 X 8}
# a2 = esp1 * a1 + eps2;   eps1, eps2 \in Rq^{12 X 8}
# ct1 = a1*s+e1;           s, e1 \in Rq^{8 X 1}
# ct2 = a2*s+e2+p*(s1|x1|x2);      e2 \in Rq^{12 X 1}
#
######################

n_Enc = d*8 # set minimal to get sufficient hardness
tau = 3     # inf-norm bound on r_i, e_i, eps1 and eps2

# Decryption must hold for ri's, ei's that can be as large as
# guaranteed by the ZK proof, i.e.,
# ||ri,ei1, ei2|| <= tau*sqrt(2*n_Enc+3*n_F)
# Independently, the sk eps1, eps2 is generated by the
# challenger and satisfies ||eps1,eps_2||_oo <= tau.
# We must have || eps1*s+e2-eps2*e1 ||_oo < p/2
# same for the randomness of ct2
boundp= sqrt(2*n_Enc)*tau**2*sqrt(2*n_Enc+3*n_F) + tau*sqrt(2*n_Enc+3*n_F)
p = ceil(2*boundp)
print('p:', p)

# We must have || eps1*r1+e2_1-eps2*e1_1 + p(s11||x1) ||_oo < q_enc/2
boundq = ceil(2*(p/2. + p*(max(beta_inf,tau_x))))

# We set q_enc = q_s * q1, with four conditions:
# (0) q1 prime
# (1) lamb*log(q1, 2) >= 128
# (2) (x^d+1) has two factors mod q1
# (3) q_enc > boundq
lamb = 10
lgq1 = 128./lamb
q1 = 7187
# Maple code: q1 := 7187: d:=128: l := numelems((Factors(x^d + 1) mod q1)[2]): isprime(q1), l;
# Maple answer is true, 2
assert(log(q1)/log(2)>=lgq1)
assert(q1<q_s)
q = q_s *  q1 # q = 88407287
print('boundq:', boundq)
print('     q:', q)

assert(q>=boundq), 'encryption q is too small'


# Hardness of LWE instance from encryption
lwe_enc_primal = MLWE_optimize_attack(q, n_Enc, n_Enc+2*n_F, tau, cost_attack=LWE_primal_cost, cost_svp=svp_classical, verbose=False)
print('LWE encryption primal:', lwe_enc_primal)
#lwe_enc_dual = MLWE_optimize_attack(q, n_Enc, n_Enc+512, tau, cost_attack=LWE_dual_cost, cost_svp=svp_classical, verbose=False)
#print('LWE encryption dual:', lwe_enc_dual)



#####################
# ZK proof    (see LNP22, Fig. 10)
# zk_secret s_zk = [s1 | x1 | x2 | s]
# E1 = [1 & 000 // h & -h' & -1 & 0 ] (for s1, s2 small)
# norm bound for E1: beta
# E2 = [0100 // 0010]  (for x1, x2 small)
# norm bound for E2: sqrt(2*n_F)*tau_x
# E3 = [000 1 // 000 & a1 // p & p & p & a2]  (for s, e1, e2 small)
# norm bound for E3: sqrt(2*n_Enc+3*n_F)*tau
#####################

# in the unforgeability proof, we replace h' by y1*h+y2, where y1 and y2 have
# infinity norms tau_x, like x1 and x2.
# the extracted one-more-isis solution is (s1+x1y1 , s2+x1*y2+x2)
# below is its norm, which is hopefully not too large compared to beta
extracted_beta = sqrt(beta**2 + tau_x**4 *  n_F * 4 + tau_x**2 * n_F * 2)

ve = 3 # number of norm equations
vd = 0 # number of inf-norm equations
norm_x = sqrt(ve)*sqrt(d)

# norm of [s1 & x1 & x2 & s] as per Thm. 5.3 (Fig. 10), in Thm.4.2 (Fig. 6) s1||z1 -> [s1 || z1 ||x]
# divide beta**2 by two since we commit only to the first half of (s1,s2)
norm_szk = sqrt( (beta**2)/2 + 2*(tau_x^2*n_F) + tau**2*n_Enc)
#norm of the norm vector s^(e) = [s1| s2 | x1 | x2 | s | e1 | e2 | x)
alpha_e = sqrt(beta**2 + 2*tau_x**2*n_F + tau**2*(2*n_Enc+3*n_F)  + norm_x**2)
print('alpha_e:', alpha_e)

gamma_e = 3
t       = 1.64
kappa   = 2
Be = 2*sqrt(256/26)*t*gamma_e*sqrt(337)*(alpha_e+sqrt(ve*d)) # as per Thm. 5.3
ce = d*(round(2*n_F/d)+1+round(2*n_F/d)+1+round((2*n_Enc+3*n_F)/d)+1) # Fig 10
print('ce:', ce)
lb1 = floor(Be*41*ce)+1                      # Thm. 5.3
lb2 = floor(Be**2+sqrt(ve*d)*Be)+1           # Thm. 5.3
beta1 = beta                                 # ||(s1,s2)||
beta2 = sqrt(2*n_F)*tau_x                    # ||(x1,x2)||
beta3 = tau*sqrt(2*n_Enc+3*n_F)              # ||(s,e1,e2)||
lb3 = floor(Be**2+3*(max(beta1, beta2, beta3))**2)  # Thm. 5.3
lb = max(lb1, lb2, lb3)

# q_zk = q * q3  = q_s * q1 * q3
# We want
# (0) q3 prime
# (1) q3 >= q1 (q1 should remain the smallest factor of q_zk)
# (2) q_zk>= lb
# (3) (x^d+1) has two factors mod q_zk <-- cannot check this is sage/python.
q3 = 124781   #nextprime(nextprime(ceil(lb/q)))
# Maple code: q3 := 124781: d:=128: l := numelems((Factors(x^d + 1) mod q3)[2]): isprime(q1), l;
# Maple answer is "true, 2"
q_zk = q*q3
assert(q_zk>=lb)
assert(q3>=q1)
print('q3:', q3)
print('log(q_zk):', log(q_zk,2), 'q_zk:', q_zk)

l = 2 # number of factors of (x^128+1) mod q1
kappa_bound = (1./(2*sqrt(l)))*(q1)**(1./l)
# The sigma_{-1} row of Fig 3 can be used if kappa < kappa_bound
assert(kappa < kappa_bound)
print('kappa bound:', kappa_bound)

#summary of all the params
#  We are somewhat free to choose n and m2
#  For MLWE to make sense we require m2>n+{0,1,2}*(256/d+1)+lamb/2+ell,
# m1 = len([s1|x1|x2])+len(s) + ve = (4+4+4)+8+3 = 23 (here s is the encryption secret)
onemoresis = {'d': 128, 'n': 10, 'm1': 23, 'm2': 34, 'q': q_zk, 'lambda': lamb, 'nu': 1, 'eta': 56, 'gamma1': 11, 'gamma2': 1.85, 'gammae': 3, 'alphae':(alpha_e)**2, 'norm_s1': norm_szk**2, 'ell': 0, 've': 3, 'vd': 0, 'D': 22}
scalar = 1
assert(onemoresis['m2']>onemoresis['n']+scalar*(256/d+1)+onemoresis['lambda']/2+onemoresis['ell']+2)

# sizes
proof = proof_size(onemoresis)
print('proof size:', proof)
ct_size = (3/2.)*n_Enc*log(q,2)/(8.*Kilo)
print('ct size:', ct_size)
print('overall non optimized:', (ct_size+proof[0]))
print('overall+CUT:', (ct_size+proof[2]))
#print('overall BG-optimized:', (ct_size+proof[1]))
#print('overall BG-optimized+CUT:', (ct_size+proof[3]))

# number of repetitions (rejection sampling)
# See [LNP22] Section 6.2  (12 is erroneous and should be 14)
reps = 2*exp(14/onemoresis['gamma1'] + 1/(2*onemoresis['gamma1']**2) + 1/(2*onemoresis['gamma2']**2) + 1/(2*onemoresis['gammae']**2))
print('avg nbr of repeats:', reps)


# security
sis_sec = SIS_security(onemoresis)
print('SIS hardness:', sis_sec)
lwe_sec = LWE_security(onemoresis)
print('LWE hardness primal:', lwe_sec)
#lwe_sec_dual = LWE_security(onemoresis, attack=LWE_dual_cost)
#print('LWE hardness dual:', lwe_sec_dual)

#####################
# One-more-SIS security
# dimensions of the one-more-SIS problem are those of Falcon
######################

# combinatorial attack
# first 4 inputs: Falcon params, the last one: norm of the vector output by the attack
# return bit hardness of the attack
res_combinatorial = combinatorial(n_F, n_F, beta, q_s, extracted_beta)
print('combinatorial attack on one-more-SIS with beta-bound', extracted_beta, ': ', res_combinatorial)

res_lattices = lattice_attack(n_F, n_F, q_s, extracted_beta)
print('lattice attack on  one-more-SIS with beta-bound', extracted_beta, ': ', res_lattices)

not_using_the_oracle = SIS_optimize_attack(q_s, 2*n_F, n_F, extracted_beta, cost_attack=SIS_l2_cost, cost_svp=svp_classical, verbose=False)
print('Falcons forgery as SIS in ell_2:', not_using_the_oracle)
