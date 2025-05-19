# Naïve long-division style
def mont_reduce_naive(t, p, n_inv):
    for i in range(k):        # k limbs
        m = (t[i] * n_inv) & 0xFFFFFFFF
        t = t + m * p << (32*i)
    return t >> (32*k) if t >= p else t

# Fiat-Crypto generated constant-time ladder (target)
# ... students’ optimizer should derive limb-wise carry chain.

