(set-logic LIA)
(synth-fun mult12345 ((x Int)) Int)
(declare-var x Int)
;(constraint (= (mult12345 x) (* x 12345)))
(constraint (=> (> x 0) (> (mult12345 x) (* x 12344))))
(constraint (=> (> x 0) (< (mult12345 x) (* x 12346))))
(check-synth)
