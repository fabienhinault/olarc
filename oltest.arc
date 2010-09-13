; -*-arc-*-

;(load "/home/fab/arc/spec-arc/spec.arc")
;(load "/home/fab/arc/ol-arc/ol.arc")

;(print-results
;;   (describe "on lisp arc tests"
;;      (prolog
;;       (= li '(a b c))
;;       (= pair '(a . b)))
;;      (it "CAR should return the first item in a list"
;;        (is (car li) 'a)))
;     (it "toto" (is ((ttrav + list) '((a b (c d)) (e) f ())) '(a b c d e f))))
;  t)

(register-test '(suite "On Lisp Tests"
  (suite "Chap 5"
    (suite "fig 5.8  ttrav"
      ("flatten"
       ((ttrav + mklist) '((a b (c d) (e) f ())))
       (a b c d e f))
      ("count-leaves"
       ((ttrav (fn (l r) (+ l (or r 1))) 1) '((a b (c d)) (e) f))
       10)
      ("copy-list"
       ((ttrav cons) '((a b (c d) (e) f ())))
       ((a b (c d) (e) f ())))
      )
    (suite "fig 5.10 trec"
      ("flatten"
       ((trec (fn (o l r) (+ (l) (r))) mklist)  '((a b (c d) (e) f ())))
       (a b c d e f))
      )
    )
  (suite "Chap 15"
    (suite "fig 15.5"
      ("our-copy-tree"
       (on-trees (cons left right) it  '((a b (c d) (e) f ())))
       ((a b (c d) (e) f ())))
      ("count-leaves"
       (on-trees (+ left (or right 1)) 1  '((a b (c d) (e) f ())))
       ((a b (c d) (e) f ())))
      ("flatten"
       (on-trees (+ left right) (mklist it)  '((a b (c d) (e) f ())))
       ((a b (c d) (e) f ())))
      ("rfind-if"
       ((rfn rfind-if (f tree)
	 (on-trees (or left right)
		   (and (f it) it)
		   tree)
	 odd '(2 (3 4) 5)))
       3)
      ))
))