(set-logic SLIA)
 
(synth-fun f ((col1 String) (col2 String)) String
    ((Start String (ntString))
     (ntString String (firstname lastname " " "," "USA" "PA" "CT" "CA" "MD" "NY"
                       (str.++ ntString ntString)
                       (str.replace ntString ntString ntString)
                       (str.at ntString ntInt)
                       (int.to.str ntInt)
                       (str.substr ntString ntInt ntInt)))
      (ntInt Int (0 1 2
                  (+ ntInt ntInt)
                  (- ntInt ntInt)
                  (str.len ntString)
                  (str.to.int ntString)
                  (str.indexof ntString ntString ntInt)))
      (ntBool Bool (true false
                    (str.prefixof ntString ntString)
                    (str.suffixof ntString ntString)
                    (str.contains ntString ntString)))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun ithSplit ((s String) (delimiter String) (i Int)) String
    (let ((firstSpacePos Int (str.indexof s delimiter 0)))
      (let ((SecondSpacePos Int (str.indexof s delimiter (+ firstSpacePos 1))))
            (ite (= i 0)
                (ite (= firstSpacePos (- 1))
                     s ; Return the whole string, there was no space
                     (str.substr s 0 firstSpacePos))
                (ite (= i 1)
                    (ite (= firstSpacePos (- 1))
                        "" ; There was no space, so index 1 is out of bounds
                        (ite (= SecondSpacePos (- 1))
                            (str.substr s (+ firstSpacePos 1) (str.len s)) ; till the end of the String
                            (str.substr s (+ firstSpacePos 1) (- (- SecondSpacePos 1) firstSpacePos)) ; to the next space; second arg of str.substr is shift, not position
                        )
                    )
                    "" ; Unhandled values of i
                )
            )

      )
    )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-var col1 String)(declare-var col2 String)
; (constraint (= (f "University of Pennsylvania" "Phialdelphia, PA, USA")  "University of Pennsylvania, Phialdelphia, PA, USA")); (constraint (= (f "UCLA" "Los Angeles, CA") "UCLA, Los Angeles, CA, USA")); (constraint (= (f "Cornell University" "Ithaca, New York, USA") "Cornell University, Ithaca, New York, USA")); (constraint (= (f "Penn" "Philadelphia, PA, USA") "Penn, Philadelphia, PA, USA")); (constraint (= (f "University of Maryland College Park" "College Park, MD") "University of Maryland College Park, College Park, MD, USA")); (constraint (= (f "University of Michigan" "Ann Arbor, MI, USA") "University of Michigan, Ann Arbor, MI, USA"))
(constraint (=> (= (ithSplit col2 " " 2) "USA" ) (= (f col1 col2) (str.++ col1 ", " col2) ) ) ) 
(constraint (=> (distinct (ithSplit col2 " " 2) "USA" ) (= (f col1 col2) (str.++ col1 ", " col2 ", USA") ) ) )

(check-synth)
