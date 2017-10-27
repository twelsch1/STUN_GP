(set-logic ALL)
(set-option :produce-models true)

(declare-fun at1 () String)(assert (= at1 (str.at "" (- 1) )))
(declare-fun at2 () String)(assert (= at2 (str.at "" 0 )))
(declare-fun at3 () String)(assert (= at3 (str.at "" 1 )))
(declare-fun at4a () String)(assert (= at4a (str.at "a" (- 1) )))
(declare-fun at4 () String)(assert (= at4 (str.at "a" 0 )))
(declare-fun at5 () String)(assert (= at5 (str.at "a" 1 )))
(declare-fun at6 () String)(assert (= at6 (str.at "ab" 1 )))

(declare-fun contains1 () Bool)(assert (= contains1 (str.contains "" "" )))
(declare-fun contains2 () Bool)(assert (= contains2 (str.contains "asda" "" )))
(declare-fun contains3 () Bool)(assert (= contains3 (str.contains "asda" "ad" )))
(declare-fun contains4 () Bool)(assert (= contains4 (str.contains "aaa" "aa" )))
(declare-fun contains5 () Bool)(assert (= contains5 (str.contains "asda" "z" )))


(declare-fun replace1 () String)(assert (= replace1 (str.replace "" "" "as")))
(declare-fun replace2 () String)(assert (= replace2 (str.replace "asda" "" "zz")))
(declare-fun replace3 () String)(assert (= replace3 (str.replace "asda" "" "s")))
(declare-fun replace4 () String)(assert (= replace4 (str.replace "aaa" "aa" "5")))
(declare-fun replace5 () String)(assert (= replace5 (str.replace "asda" "a" "5")))

(declare-fun indexof1a () Int)(assert (= indexof1a (str.indexof "" "" 0)))
(declare-fun indexof1b () Int)(assert (= indexof1b (str.indexof "" "" (- 1))))
(declare-fun indexof1c () Int)(assert (= indexof1c (str.indexof "" "" 1)))

(declare-fun indexof2a () Int)(assert (= indexof2a (str.indexof "a" "" (- 1))))
(declare-fun indexof2b () Int)(assert (= indexof2b (str.indexof "a" "" 0)))
(declare-fun indexof2c () Int)(assert (= indexof2c (str.indexof "a" "" 1)))
(declare-fun indexof2d () Int)(assert (= indexof2d (str.indexof "a" "" 2)))

(declare-fun indexof3a () Int)(assert (= indexof3a (str.indexof "aa" "" (- 1))))
(declare-fun indexof3b () Int)(assert (= indexof3b (str.indexof "aa" "" 0)))
(declare-fun indexof3c () Int)(assert (= indexof3c (str.indexof "aa" "" 1)))
(declare-fun indexof3d () Int)(assert (= indexof3d (str.indexof "aa" "" 2)))
(declare-fun indexof3e () Int)(assert (= indexof3e (str.indexof "aa" "" 3)))

(declare-fun indexof4 () Int)(assert (= indexof4 (str.indexof "a" "b" 0)))
(declare-fun indexof5 () Int)(assert (= indexof5 (str.indexof "a" "a" 0)))
(declare-fun indexof6a () Int)(assert (= indexof6a (str.indexof "aaa" "a" (- 100))))
(declare-fun indexof6b () Int)(assert (= indexof6b (str.indexof "aaa" "a" 0)))
(declare-fun indexof6c () Int)(assert (= indexof6c (str.indexof "aaa" "a" 2)))
(declare-fun indexof6d () Int)(assert (= indexof6d (str.indexof "aaa" "a" 3)))
(declare-fun indexof7a () Int)(assert (= indexof7a (str.indexof "aaa" "aa" 0)))
(declare-fun indexof7b () Int)(assert (= indexof7b (str.indexof "aaa" "aa" 1)))
(declare-fun indexof7c () Int)(assert (= indexof7c (str.indexof "aaa" "aa" 2)))
(declare-fun indexof8 () Int)(assert (= indexof8 (str.indexof "asda" "aa" 0)))


(declare-fun substr1 () String)(assert (= substr1 (str.substr "" (- 1) 2)))
(declare-fun substr2 () String)(assert (= substr2 (str.substr "asd" (- 1) 2)))
(declare-fun substr3 () String)(assert (= substr3 (str.substr "" 0 0)))
(declare-fun substr4 () String)(assert (= substr4 (str.substr "" 0 1)))
(declare-fun substr5 () String)(assert (= substr5 (str.substr "as" (- 1) (- 1))))
(declare-fun substr6 () String)(assert (= substr6 (str.substr "asdfgh" 0 2)))
(declare-fun substr7a () String)(assert (= substr7a (str.substr "asdfgh" 0 10)))
(declare-fun substr7b () String)(assert (= substr7b (str.substr "asdfgh" 3 10)))
(declare-fun substr7c () String)(assert (= substr7c (str.substr "asdfgh" 10 10)))
(declare-fun substr7d () String)(assert (= substr7d (str.substr "asdfgh" 0 100)))
(declare-fun substr7e () String)(assert (= substr7e (str.substr "asdfgh" 0 (- 1))))
(declare-fun substr8a () String)(assert (= substr8a (str.substr "asdfgh" 3 0)))
(declare-fun substr8b () String)(assert (= substr8b (str.substr "asdfgh" 3 1)))
(declare-fun substr8c () String)(assert (= substr8c (str.substr "asdfgh" 3 2)))

(declare-fun prefixof1 () Bool)(assert (= prefixof1 (str.prefixof "" "")))
(declare-fun prefixof2 () Bool)(assert (= prefixof2 (str.prefixof "" "asd")))
(declare-fun prefixof3 () Bool)(assert (= prefixof3 (str.prefixof "asd" "")))
(declare-fun prefixof4 () Bool)(assert (= prefixof4 (str.prefixof "asd" "asd")))
(declare-fun prefixof5 () Bool)(assert (= prefixof5 (str.prefixof "asd" "asda")))
(declare-fun prefixof6 () Bool)(assert (= prefixof6 (str.prefixof "da" "asda")))

(declare-fun suffix1 () Bool)(assert (= suffix1 (str.suffixof "" "")))
(declare-fun suffix2 () Bool)(assert (= suffix2 (str.suffixof "" "asd")))
(declare-fun suffix3 () Bool)(assert (= suffix3 (str.suffixof "asd" "")))
(declare-fun suffix4 () Bool)(assert (= suffix4 (str.suffixof "asd" "asd")))
(declare-fun suffix5 () Bool)(assert (= suffix5 (str.suffixof "asd" "asda")))
(declare-fun suffix6 () Bool)(assert (= suffix6 (str.suffixof "da" "asda")))


(declare-fun strint1 () Int)(assert (= strint1 (str.to.int "" )))
(declare-fun strint2 () Int)(assert (= strint2 (str.to.int "-123" )))
(declare-fun strint3 () Int)(assert (= strint3 (str.to.int "(- 12)" )))
(declare-fun strint4 () Int)(assert (= strint4 (str.to.int "1" )))
(declare-fun strint5 () Int)(assert (= strint5 (str.to.int "1234567" )))


(declare-fun intstr1 () String)(assert (= intstr1 (int.to.str 0 )))
(declare-fun intstr2 () String)(assert (= intstr2 (int.to.str (- 123) )))
(declare-fun intstr3 () String)(assert (= intstr3 (int.to.str (- 12) )))
(declare-fun intstr4 () String)(assert (= intstr4 (int.to.str 1 )))
(declare-fun intstr5 () String)(assert (= intstr5 (int.to.str 1234567 )))

(check-sat)
(get-model)