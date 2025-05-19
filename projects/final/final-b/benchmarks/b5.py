def inv_fp2_fermat(a):        # 80 Fp muls via exponentiation
    return a ** (p2 - 2)

#def inv_fp2_short(a0, a1):    # 1 Fp inv + 3 mul + 3 add
#    t0 = a0*a0 + a1*a1        # norm
#    inv = inv_fp(t0)          # single Fp inverse
#    return (a0*inv, -a1*inv)

