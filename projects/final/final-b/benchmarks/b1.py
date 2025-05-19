# Inputs: a = (a0, a1), b = (b0, b1)  over Fp

def mul_fp2_naive(a, b):
    v0 = a0 * b0              # 4 Fp muls total
    v1 = a1 * b1
    return (v0 - v1, (a0+a1)*(b0+b1) - v0 - v1)

# Expected Karatsuba target (3 Fp muls)
# v0 = a0*b0
# v1 = a1*b1
# v2 = (a0+a1)*(b0+b1)
# return (v0 - v1, v2 - v0 - v1)

