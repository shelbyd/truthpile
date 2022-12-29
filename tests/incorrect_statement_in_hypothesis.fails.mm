$c true num happy 0 1 > $.
$v n $.

num_n $f num n $.
num_zero $a num 0 $.

one_gt_zero $a true 1 > 0 $.

${
    is_gt_ze $e true n > 0 $.
    num_happy $a happy n $.
$}

the1 $p happy 0 $= num_zero one_gt_zero num_happy $.
