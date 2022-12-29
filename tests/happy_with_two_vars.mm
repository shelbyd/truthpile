$c true num happy 0 1 > < $.
$v m n $.

$( TODO(shelbyd): Test with these two $f's switched $)
num_m $f num m $.
num_n $f num n $.

num_zero $a num 0 $.
num_one  $a num 1 $.

zero_lt_one $a true 0 < 1 $.

${
    is_gt $e true m < n $.
    num_happy $a happy n $.
$}

the1 $p happy 1 $= num_zero num_one zero_lt_one num_happy $.
