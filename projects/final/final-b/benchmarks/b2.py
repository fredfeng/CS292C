# A = a0 + a1*V  where V^2 = ξ  (Fp² coefficients)
def sq_fp4_naive(a0, a1, xi):
    c0 = a0*a0 + (a1*a1)*xi   # 2 sqr + 1 mul + ξ-mul
    c1 = 2 * a0 * a1
    return (c0, c1)

def sq_fp4_optimized(a0, a1, xi):
    t0 = a0*a0
    t1 = a1*a1
    c0 = t1 * xi + t0
    c1 = (a0 + a1)**2 - t0 - t1
    return (c0, c1)           # 3 sqr, no general mul

