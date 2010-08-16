NUMS = [5213588008354709077L, 9011219417469017946L,
        9115813602317594993L, 1796745334760975384L,
        2375118318707634486L, 3579709154995762145L,
        2312952310307873817L, 3627590721354606439L,
        5941472576423725122L, 4317696052329054505L,
        5763055694478716846L, 5226146329630268999L,
        2730952213106576953L, 6235647640047602135L,
        5014371167157923471L, 4868653895375087301L,
        9737387704190733086L, 9262565481673300485L,
        5968266991171521006L, 6752113930489992229L,
        5917882775011418152L, 5866436908055159779L,
        9233099989955257688L, 9376338948688351159L,
        3772194655144630358L, 9029836747496103755L,
        3318990262990089104L, 9205546877037990475L,
        9498032114812022495L, 9990105869964955299L,
        9849598364470384044L, 2664344232060524242L,
        1376783969573792128L, 1108556560089425769L,
        7820574110347009988L, 1603454130529647419L,
        6951628222196921724L, 9889945707884382295L,
        4776591302180789869L, 7652184907611215542L,
        3982809542974920136L, 8082643935949870308L,
        1233783467857668500L, 4271233363607031147L,
        7999940522596325715L, 1509145775275864006L,
        6415171202616583365L, 4143260390225524497L,
        6393762352694839041L, 2290598705560799669L,
        7835010686462271800L, 8505865989334316749L,
        7547888419188030222L, 4408107167048106771L,
        8998470433081591390L, 9131522681668251869L,
        9096632376298092495L, 7481066850797885510L,
        5295758362772474604L, 1796212605533609345L,
        5953431042043343946L, 3151838989804308537L,
        6445353832659195698L, 9929081270845451034L,
        6422250272800292361L, 8643312627450063997L,
        7207546018039041794L, 3624820335477016277L,
        3782849199070331143L, 6012991563467874119L]

def get_byte_str(hex_str):
    from binascii import unhexlify
    return unhexlify(hex_str)

def get_bit_str(byte_str):
    return ''.join('1' if ord(byte_str[i // 8]) & (1 << (i % 8)) else '0'
                   for i in range(8 * len(byte_str)))

def get_indices(byte_str):
    return [i for i in range(8 * len(byte_str))
            if ord(byte_str[i // 8]) & (1 << (i % 8))]

def get_subset(indices):
    return [NUMS[i] for i in indices]

def get_subset_str(byte_str):
    sset_str = [str(n) for n in get_subset(get_indices(byte_str))]
    if len(sset_str) % 2:
        sset_str.append('')
    return '\n'.join('%s %s' % (sset_str[i], sset_str[i + 1])
                     for i in range(0, len(sset_str), 2))

def get_indices_str(byte_str):
    return ', '.join(str(i) for i in get_indices(byte_str))

def get_subset_sum(byte_str):
    return sum(get_subset(get_indices(byte_str)))

if __name__ == '__main__':
    while True:
        hex_str = raw_input('Hex subset: ')
        byte_str = get_byte_str(hex_str)
        print 'Bit string: %s' % get_bit_str(byte_str)
        print 'Indices: %s' % get_indices_str(byte_str)
        print 'Subset:\n%s' % get_subset_str(byte_str)
        print 'Sum: %d' % get_subset_sum(byte_str)
