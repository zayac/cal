(: a: 10, b: [35, 42, {}, nil], c: t :) <= (: b: $k | $x :);
[$l, $x ] <= [$a, $b | $a];
[$a, $b] <= [[35], (: c : t | $d :)];
{ q: $d, r: $d } <= { r : (: a : nil, aa: 10 :)};
