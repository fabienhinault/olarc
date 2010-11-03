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
  (suite "Chap 4"
    (suite "fig 4.2"
      ("group"
       (group '(a b c d e f g) 2)
       ((a b) (c d) (e f) (g)))
      )
    )
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
       (on-trees (cons (left) (right)) it  '((a b (c d) (e) f ())))
       ((a b (c d) (e) f ())))
      ("count-leaves"
       (on-trees (+ (left) (or (right) 1)) 1  '((a b (c d) (e) f)))
       10)
      ("flatten"
       (on-trees (+ (left)(right)) (mklist it)  '((a b (c d) (e) f ())))
       (a b c d e f))
      ("rfind-if"
       ((rfn rfind-if (f tree)
	 (on-trees (or (left) (right))
		   (and (f it) it)
		   tree))
	 odd '(2 (3 4) 5))
       3)
      )
    (suite "fig 15.7"
      ("lazy evaluation"
       (force 'a)
       a)
      ("2"
       (do
	 (let x 2
	   (= d (delay (+ 1 x))))
	 (force d))
       3)
      )
    )
  (suite "Chap 16"
    (suite "fig 16.1"
      ("abbrev"
	 (zza nil nil)
       nil)
      ("abbrevs"
       (do
	 (abbrevs wwa and www with wwl let)
	 (macex1 '(wwl)))
       (let))
      )
    (suite "fig 16.3 anaphoric macros"
      ("a+"
       (< (abs (- (mass-cost 7.95) 9.54)) 1.0e-10)
       t)
      ("alist analist"
       (analist 1 (+ 2 it) (+ 2 it))
       (1 3 5))
      )
    )
  (suite "Chap 18"
    (suite "fig 18.1"
      ("dbind"
       (dbind (a (b . c) . d) '(1 "fribble" 2 3 4) (list a b c d))
       (1 #\f "ribble" (2 3 4))))
    (suite "fig 18.7"
      ("efficient if-match"
       (if-match (?x (1 . ?y) . ?x) '((a b) (1 2 3) a b)
               (list ?x ?y))
       ((a b) (2 3)))
      ("abab list"
       (abab '(hi ho hi ho))
       (hi ho))
      ("abab string"
       (abab "abab")
       (#\a #\b)))
    )
  (suite "Chap 19"
    (suite "fig 19.5"
      ("The first name and nationality of every painter called Hogarth."
       (let l nil (w/answer (painter hogarth ?x ?y) (push (list ?x ?y) l)) l)
       ((william english)))
      ("The last name of every painter born in 1697."
       (let l nil (w/answer (and (painter ?x _ _)
                                 (dates ?x 1697 _))
                            (push ?x l)) l)
       (hogarth canale))
      ("The last name and year of birth of everyone who died in 1772 or 1792."
       (let l  nil (w/answer (or (dates ?x ?y 1772)
                               (dates ?x ?y 1792))
                           (push (list ?x ?y) l))
            l)
       ((reynolds 1723) (hogarth 1697)))
      ((+ "The last name of every English painter not born the same year "
         "as a Venetian one.")
       (let l nil (w/answer (and (painter ?x _ english)
                                 (dates ?x ?b _)
                                 (not (and (painter ?x2 _ venetian)
                                           (dates ?x2 ?b _))))
                            (push ?x l))
            l)
       (reynolds))
      ))
;2 closing parentheses after the chapter suites
)) ;(register-test '(suite "On Lisp Tests"