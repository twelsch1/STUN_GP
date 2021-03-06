(set-logic QF_NRA)
(synth-fun gravity ((m1 Real)(m2 Real)(r Real)) Real)
(declare-var m1 Real)
(declare-var m2 Real)
(declare-var r Real)
(constraint (= (gravity 8.16229 6.08439 5.22398) 0.0000000006344739000317563))
(constraint (= (gravity 8.06439 4.04148 2.69657) 0.0000000008066524554078432))
(constraint (= (gravity 3.09435 6.42601 5.6744) 0.00000000023387138493288976))
(constraint (= (gravity 5.578 2.66 4.39986) 0.0000000002250647555149482))
(constraint (= (gravity 7.77423 5.81167 9.50776) 0.0000000003171511737029578))
(constraint (= (gravity 4.16544 0.3516 6.05325) 0.000000000016147576145865443))
(constraint (= (gravity 3.13934 3.47749 2.07122) 0.00000000035177438683166636))
(constraint (= (gravity 7.51421 6.42235 1.46384) 0.000000002200239159505267))
(constraint (= (gravity 0.92058 0.12468 4.82468) 0.0000000000015877276849565152))
(constraint (= (gravity 10.96208 6.70522 2.03141) 0.0000000024148747760246446))

(constraint (and
    (=> (and (and (>= m1 2.5) (<= m1 12.0))) (= (gravity m1 m2 r) (gravity m2 m1 r)))
    (=> (and (and (>= m1 0.5) (<= m1 10.0))) (>= (gravity m1 m2 r) 0.0))))
(check-synth)
