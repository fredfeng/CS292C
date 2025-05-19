def easy_part_naive(p):       # repeated Frobenius & mul
    return p ** ((p**4 - p**2 + 1))

# Compressed method (Karabina) with fewer Fp⁶ muls
# Students synthesize series of Frobenius maps + squarings

