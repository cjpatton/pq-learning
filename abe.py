from sage.all import GF, ceil, log, matrix

# Gadget Trapdoors (2015/939, Section 5.4.3)

def gadget(n, q):
    l = ceil(log(q) / log(2))
    F = GF(q)
    rows = []
    for i in range(n):
        row = []
        for j in range(n):
            if i == j:
                row += [F(2**k) for k in range(l)]
            else:
                row += [F(0)] * l
        rows.append(row)
    return matrix(rows)

print(gadget(4, 101))
