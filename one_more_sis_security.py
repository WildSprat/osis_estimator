
##
##  One-more-SIS security estimators
##

from math import sqrt, floor, ceil, log, exp
from model_BKZ import BKZ_first_length, delta_BKZ, svp_classical
pi = 3.1415926535897932384626433832795028841971693993751058209749

# As per Fig.3:
#  combining n/w y's from the preimage queiries,
#  obtain a vector of norm <= sqrt(n/w)*len_y
def combinatorial(n, m, len_y, q, output_norm):
    """
        C \in Z_q^{n \times m} as per definition of one-more-SIS
        len_y       -- l2-norm of vectors returned in preimage queries
        output_norm -- l2_norm of the vectors the attack outputs

    """
    w = ceil(n*len_y/output_norm)
    return 2*log(n)+w*log(q,2)

#
#   BKZ-beta returns a vector of norm <= delta_beta^m*sqrt(m)*q^n/m
#   We also search for m that minimizes the norm
#
def lattice_attack(n, m, q, output_norm):
    m_ = m
    log_norm = log(output_norm)
    beta_min = m
    m_min = m
    while m_ > 100:
        #find bkz_beta that achievs output_norm
        beta_ = 30
        while beta_<m:
            #print(beta_, m_*log(delta_BKZ(beta_))+0.5*log(m_)+(n/m_)*log(q))
            if  m_*log(delta_BKZ(beta_))+(n/m_)*log(q) > log_norm:
                beta_+=10
            else:
                if beta_<beta_min:
                    beta_min = beta_
                break
        m_-=50
    #print('beta_min:', beta_min)
    return svp_classical(beta_min)

n     = 2*512
m     = n
q     = 12301
sec   = 128
epsinv = sqrt(sec*2**64)
sigma_F = (1/pi)*sqrt(log(4*512*(1+epsinv))/2)*1.17*sqrt(q)
len_y = sigma_F*1.1*sqrt(n)


#res_combinatorial = combinatorial(n, m, len_y, q, 30*len_y)
#print('combinatorial:', res_combinatorial)

#res_lattices = lattice_attack(n, m, q, 30*len_y)
#print('lattices:', res_lattices)
