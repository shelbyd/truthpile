$c 0 + = -> ( ) term wff |- $.
$v t r s P Q $.

tt $f term t $.
tr $f term r $.
ts $f term s $.
wp $f wff P $.
wq $f wff Q $.

tze $a term 0 $.
tpl $a term ( t + r ) $.

weq $a wff t = r $.
wim $a wff ( P -> Q ) $.

a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.
a2 $a |- ( t + 0 ) = t $.

${
   min $e |- P $.
   maj $e |- ( P -> Q ) $.
   mp  $a |- Q $.
$}

th1 $p |- t = t $=
  ( tze tpl weq a2 wim a1 mp ) ABCZADZAADZAEZJJKFLIAAGHH $.
