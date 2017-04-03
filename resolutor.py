import subprocess
def run_4ti2(command, data, results):
    """Run 4ti2 and """
    #cleanup_42()
    setup_42(data)
    s = subprocess.call(
        ["./%s %s"% (command, TMPF)],
        shell=True,
        # stdout=subprocess.PIPE,
        # stderr=subprocess.PIPE,
    )
    if s:
        raise  RuntimeError("ha fallado 4ti2")

    return [load_42_matrix(r) for r in results]

def load_42_matrix(ext):
    """docstring for load_42_matrix"""
    with open(TMPF+ext) as f:
        s=f.read().splitlines()
    return [line_to_list(l) for l in s[1:]]


def write_42_file(ext, string):
    """docstring for write_42"""
    fname = TMPF + ext
    with open(fname, 'w') as f:
        f.write(string)

def matrix_to_42(A):
    """Print a representation of matrix M as 4ti2 input. M should be an integer matrix."""
    M = matrix(ZZ,A)
    n, m = M.dimensions()
    return "%s %s\n" % (n,m) + "\n".join([row_to_42(r) for r in M.rows()]) + "\n"

def row_to_42(r):
    """Convert a vector to 4ti2 input format. Should be an integer vector"""
    return  " ".join([str(i) for i in r])

def setup_42(data):
    for (k, s) in data.iteritems():
        write_42_file(k,s)
        

def bigsolve(A,b,c,u):

    (d,n)=A.dimensions()

    lower = identity_matrix(n).augment(zero_matrix(n,d)).augment(identity_matrix(n))

    bigA = A.augment(identity_matrix(d)).augment(zero_matrix(d,n)).stack(lower)
    bigb = matrix(b).augment(matrix(c))
    bigc = matrix(c).augment(zero_matrix(1,n+d))


    zsol = vector(ZZ,n*[0]+list(b)+n*[1])
    #bigA, bigb, bigc, zsol
    data = {
        ".mat": matrix_to_42(bigA),
        ".zsol": matrix_to_42(matrix(zsol)),
        ".cost": matrix_to_42(-matrix(bigc))
    }
    GG = matrix(ZZ,run_4ti2("../42/pruebas/groebner -t lp", data, [".gro"])[0])[:,0:n]
    return GG.rows()

def line_to_list(s):
    """docstring for line_to_list"""
    return [Integer(i) for i in s.strip().split()]


TMPF = "temporary_file__"

