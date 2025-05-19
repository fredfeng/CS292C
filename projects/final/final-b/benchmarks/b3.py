# Elements as (x0,x1,x2), (y0,y1,y2) over Fp²  with U^3 = ξ
def mul_fp6_naive(x, y, xi):
    # schoolbook: 18 Fp² muls
    z0 = x0*y0 - (x1*y2 + x2*y1)*xi
    z1 = x0*y1 + x1*y0 - x2*y2*xi
    z2 = x0*y2 + x1*y1 + x2*y0
    return (z0, z1, z2)

# Optimized lazy-Frobenius & Karatsuba version (11 muls)
# ... students' tool should rediscover

