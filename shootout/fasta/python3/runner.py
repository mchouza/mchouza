import os, time

BLOCK_SIZE = 2 ** 16

BASE_N = 1000
BASE_FN = 'fasta-output.txt'

N_VALUES = (250000, 2500000, 25000000)
#N_VALUES = (250000, 2500000)

PYTHON3_PATH = r'C:\Python32\python.exe'

def run_fasta_script(fn, n, output_fn):
    os.system('%s %s %d >%s' % (PYTHON3_PATH, fn, n, output_fn))

def are_files_equal(fn1, fn2):
    fp1 = open(fn1)
    fp2 = open(fn2)
    data1 = data2 = True
    while data1 and data1 == data2:
        data1 = fp1.read(BLOCK_SIZE)
        data2 = fp2.read(BLOCK_SIZE)
    return data1 == data2

def test_fasta(fn):
    print('Testing "%s"...' % fn)

    print('Checking correctness...', end=' ')
    base_output_fn = '%s.base.output.txt' % fn
    run_fasta_script(fn, BASE_N, base_output_fn)
    if not are_files_equal(BASE_FN, base_output_fn):
        print('FAIL')
    else:
        print('OK')

    print('Checking times for different values of N:')
    for n in N_VALUES:
        print('  N = %d:' % n, end=' ')
        output_fn = '%s.%d.output.txt' % (fn, n)
        start = time.time()
        run_fasta_script(fn, n, output_fn)
        print('%f s' % (time.time() - start))
    print()

def main():
    for fn in os.listdir('.'):
        if fn.startswith('fasta') and fn.endswith('.py'):
            test_fasta(fn)

if __name__ == '__main__':
    main()
