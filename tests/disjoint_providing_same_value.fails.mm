$c true num 0 1 != $.
$v x y $.

num_x $f num x $.
num_y $f num y $.

num_zero $a num 0 $.
num_one  $a num 1 $.

${
	$d x y $.
    x_ne_y $a true x != y $.
$}

the1 $p true 0 != 0 $=
    num_zero num_zero x_ne_y $.
