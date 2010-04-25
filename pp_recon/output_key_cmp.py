"""Compares the generated output file with the testcase key file.

Compares the generated output file ('output.txt') with the testcase key file
('key.txt'), printing the number and kind of differences (errors) found."""

DETAILED = True

def cmp_lines(key_line, output_line):
    """Returns -1 if there is a false negative, +1 if a false positive or 0 if
    they match."""

    key_basic_line = key_line.split('#')[0].strip()
    output_basic_line = output_line.strip()

    assert key_basic_line in ('YES', 'NO')
    assert output_basic_line in ('YES', 'NO')
    
    if key_basic_line == output_basic_line:
        return 0
    elif key_basic_line == 'YES':
        return -1
    elif key_basic_line == 'NO':
        return +1
    
    assert 0

def main():
    key_fp = open('key.txt')
    output_fp = open('output.txt')
    num_lines = 0
    false_positives = 0
    false_negatives = 0
    for l1, l2 in zip(key_fp, output_fp):
        cmp_result = cmp_lines(l1, l2)
        num_lines += 1
        if cmp_result < 0:
            false_negatives += 1
            if DETAILED:
                print 'False negative at line %d' % num_lines
        elif cmp_result > 0:
            false_positives += 1
            if DETAILED:
                print 'False positive at line %d' % num_lines
    key_fp.close()
    output_fp.close()
    print '%d errors: %d false positives and %d false negatives.' %\
          (false_positives + false_negatives, false_positives, false_negatives)

if __name__ == '__main__':
    main()
