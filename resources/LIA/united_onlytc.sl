(set-logic LIA)
(synth-fun united ((a Int)) Int)
(declare-var x Int)
(constraint (= (united 1) 5))
(constraint (= (united 3) 3))
(constraint (= (united 7) 10))
(constraint (= (united 13) 15))
(check-synth)
