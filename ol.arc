;-*-arc-*-

;chap 4
;fig 4.1
(def mklist (x)
  (if (alist x) x (list x)))

;fig 4.2
(def group (source n)
  (when (is 0 n)(error "zero length"))
  (if (no source)
      nil
      ((afn (source acc)
	(let rest (nthcdr n source)
	  (if (acons rest)
	      (self rest (cons (cut source 0 n) acc))
	      (rev (cons source acc)))))
       source nil)))


(def prune (test tree)
  (if (no tree)         nil
      (acons:car tree)  (cons (prune test (car tree)) (prune test (cdr tree)))
      (test:car tree)   (prune test (cdr tree))
                        (cons (car tree) (prune test (cdr tree)))))

(def before (x y l)
  (and l
       (let first (car l)
          (if (is y first) nil
              (is x first) l
                           (before x y (cdr l))))))

(def after (x y l)
  (let rest (before y x l)
     (and rest (mem x rest))))

(def duplicate (o l)
  (mem o (cdr (mem o l))))

(def split-if (f l)
  ((afn (acc src)
     (if (or (no src) (f:car src)) 
         (list (rev acc) src)
         (self (cons (car src) acc) (cdr src))))
    nil l))

(def most (f l)
  ((afn (wins max src)
      (if (no src) 
          (list wins max)
          (let score (f:car src)
            (if (> score max)
                (self (car src) score (cdr src))
                (self wins max (cdr src))))))
    (car l) (f:car l) (cdr l)))

(def mostn (f l)
  (if (no l)
      nil
      (withs (res (list:car l) max (f:car l))
         (each elt (cdr l)
            (let score (f elt)
               (if (> score max)  (= max score res (list elt)) 
                   (is score max) (push elt res))))
         (rev res))))

;; (def range (n)
;;   (let res nil
;;     (down i (- n 1) 0
;;        (= res (cons i res)))
;;     res))


(def mapa-b (f a b (o step 1))
   (if (> a b)
       nil
       (cons (f a) (mapa-b f (+ step a) b step))))

(def map0-n (f n)
  (mapa-b f 0 n))

(def map1-n (f n)
  (mapa-b f 1 n))

(def map-> (f start test-fn succ-fn)
  (if (test-fn start)
      nil
      (cons (f start) (map-> f (succ-fn start) test-fn succ-fn))))

(def mapcars (f . ls)
  (let res nil
     (each l ls
        (each elt l
          (push (f elt) res)))
     (rev res)))

(def mapcars (f . ls)
  (accum a
     (each l ls
        (each elt ls
           (a (f elt))))))

(def rmap (f . args)
  (if (some atom args)
      (apply f args)
      (apply map (fn xs (apply rmap f xs)) args)))

(def readlist ()
  (readstring1 (+ "(" (readline) ")")))

(mac prompt args
  `(do
     (prf ,@args)
     (read)))

(mac break-loop (f quit . args)
  (w/uniq in
    `(do
        (prf "Entering break-loop.\n")
        (whiler ,in (prompt ,@args) ,quit
          (prf "~\n\n" (,f ,in))))))


(def symb args
  (sym (apply string args)))

(def reread args
  (read (apply string args)))

(def explode (sy)
  (let res nil
    (each s (string sy)
      (push (sym s) res))
    (rev res)))

(def explode (sy)
  (accum a
    (each c (string sy)
      (a (sym c)))))


(= *equivs* (table))

(def ff (f)
  (or (*equivs* f) f))

(def deff (f ff)
  (= (*equivs* f) ff))

(def memoize (f)
  (let cache (table)
     (fn args
        (iflet val (cache args)
            val
            (= (cache args) (f args))))))

(def fif (test then (o else))
  [if (test _) (then _) (else _)])

(def fint (f . fs)
  (if (no fs)
      f
      [and (f _)((fint fs) _)]))

(def fun (f . fs)
  (if (no fs)
      f
      [or (f _)((fun fs) _)]))

(def fn0ify (x)
  (if (isa x 'fn) (x) x))

(def callif (x)
  (if (isa x 'fn) (x) x))

(def fn? (x)
  (isa x 'fn))

(def lrec (rec base)
  (afn (l)
     (if (no l)
         (fn0ify base)
         (rec (car l) (fn () (self:cdr l))))))

;fig 5.8
 
(def ttrav (rec (o base idfn))
  (afn (tree)
    (if (atom tree)
	(if (fn? base)
	    (base tree)
	    base)
	(rec (self:car tree)
	     (when (cdr tree) (self:cdr tree))))))

(def trec (rec (o base idfn))
  (afn (tree)
    (if (atom tree)
	(if (fn? base)
	    (base tree)
	    base)
	(rec tree
	     (fn ()(self:car tree))
	     (fn ()(when (cdr tree) (self:cdr tree)))))))
    

(= nodes* (table))

;chap 6

(def defnode (name conts (o yes nil) (o nope nil))
     (= (nodes* name)
	(list conts yes nope)))


(def run-node (name)
     (let n (nodes* name)
	  (if (cadr n)
	      (do 
	       (prf "~\n\n" (car n))
	       (case (read)
		     yes (run-node (cadr n))
		         (run-node (car:cddr n))))
	    (car n))))

(def defnode (name conts (o yes nil) (o nope nil))
     (= (nodes* name)
	(if yes
	    (fn () 
		(prf "~\n\n" conts)
		(case (read)
		      yes ((nodes* yes))
                          ((nodes* nope))))
	  (fn () conts))))

(= nodes* nil)

(def defnode args
     (push args nodes*)
     args)

(def compile-net (root)
     (let node (assoc root nodes*)
	  (if (no node)
	      nil
	    (with (conts (cadr node)
		   yes   (car:cddr node)
		   nope  (car:cddr:cdr node))
		  (if yes
		      (with (yes-fn (compile-net yes)
			     no-fn (compile-net nope))
			    (fn ()
				(prf "~\n\n" conts)
				(if (is (read) 'yes)
				    (yes-fn)
				  (no-fn))))
		    (fn () conts))))))

(defnode 'people "Is the person a man?" 'male 'female)
(defnode 'male "Is he living" 'liveman 'deadman)
(defnode 'deadman "Was he American?" 'us 'them)
(defnode 'us "Is he on a coin?" 'coin 'cidence)
(defnode 'coin "Is the coin a penny?" 'penny 'coins)
(defnode 'penny 'lincoln)

;----------------------------------------
;matches

(def nth (l . args)
  (if (no (cdr args))
      (car (nthcdr (car args) l ))
	 (apply nth (cons (nth l (car args)) (cdr args)))))

(def index-subst (l index new)
  (if (is index 0)
      (cons new (cdr l))
    (cons (car l) (index-subst (cdr l) (- index 1) new)))) 

(def isapos (l)
  (and (alist l) (is (len l) 4) (all [isa _ 'int] l))) 

(def flatp (l pred)
  ((afn (x xpred acc)
     (if (no x)   acc
         (xpred x) (cons x acc)
                  (self (car x) xpred (self (cdr x) xpred acc))))
   l pred nil))

(def treewisep (f base tree pred)
  (if (pred tree)
      (base tree)
      (f (treewisep f base (car tree) pred)
	 (treewisep f base (cdr tree) pred))))

(def apply-move (initial line taken)
  (let newNb (- (car:nthcdr line initial) taken)
    (when (>= newNb 0)
      (index-subst initial line newNb))))
	  
;arc0 impl			  
;; (defmemo next-positions (l)
;;   (rev 
;;     (accum a
;;       (forlen line l
;; 	(a 
;; 	  (rev  
;; 	    (accum b
;; 	      (each taken (range 1 3)
;; 		(aif (apply-move l line taken)
;; 		     (b it))))))))
;;     )) ;arc0

(defmemo next-positions (l)
  (accum a
    (forlen line l
      (a (accum b
	   (each taken (range 1 3)
	     (aif (apply-move l line taken)
		  (b it))))))))

;arclite impl
;; (def display (l)
;;   (each i l 
;;     (repeat i (pr "I"))
;;     (pr "\n")))

(def display (l)
  (let i 1
    (each matches l
      (prf  "~  " i)
      (repeat matches (pr "I"))
      (pr "\n")
      (++ i))))

(defmemo find-loosing(pos)
  (let l (flatp (next-positions pos) isapos)
    (if (no l)
         nil
      (find ~find-loosing l))))

(def ask-move (l)
  (if (iso l '(0 0 0 0))
      (do (display '(0 0 0 0))(prn "Perdu !"))
    (do
      (display l)
      (pr "ligne?")
      (= line (read))
      (pr "nombre d'alumettes (1, 2 ou 3)?")
      (= taken (read))
      (play (apply-move l (- line 1) taken)))))

(def play (l)
  (if (iso l '(0 0 0 0))
      (prn "Bravo !")
    (withs (lnextpos (next-positions l)
	    loosing (find-loosing l))
      (display l)
      (prn "---------------")
      (if (no loosing) 
	  (ask-move (rand-elt (flatp lnextpos isapos)))
	(ask-move loosing)))))

(def alumettes-simple ()
  (let l '(6 5 4 3)
    (display l)
    (prn "Tapez 'l' pour me laisser commencer, sinon le numéro de ligne.")
    (= line (read))
    (if (is line 'l)
	(play l)
	(do
	  (pr "nombre d'alumettes (1, 2 ou 3)?")
	  (= taken (read))
	  (play (apply-move l (- line 1) taken))))))

(defmemo compile-ask-move (l)
  (if (iso l '(0 0 0 0))
	(fn () (display '(0 0 0 0))(prn "Perdu !"))
      (let tnext-fns (treewisep cons 
				[if (no _) nil (compile-position _)]
				(next-positions l) 
				[or (no _) (isapos _)])
	(fn ()
	  (display l)
	  (pr "ligne?")
	  (= line (read))
	  (pr "nombre d'alumettes (1, 2 ou 3)?")
	  (= taken (read))
	  ((nth tnext-fns (- line 1) (- taken 1)))))))

(defmemo compile-position (l)
  (if (iso l '(0 0 0 0))
      (fn () (prn "Bravo !"))
	  (withs (lnextpos (next-positions l)
		  loosing (find-loosing l)
		  ask-fn (if (no loosing) 
			     (compile-ask-move (rand-elt (flatp lnextpos isapos)))
			   (compile-ask-move loosing)))
	    (fn ()
	      (display l)
	      (prn "---------------")
	      (ask-fn)))))

(def alumettes ()
  (let l '(6 5 4 3)
    (display l)
    (prn "Tapez 'l' pour me laisser commencer, sinon le numéro de ligne.")
    (= line (read))
    (if (is line 'l)
	((compile-position l))
	(do
	  (pr "nombre d'alumettes (1, 2 ou 3)?")
	  (= taken (read))
	  ((compile-position (apply-move l (- line 1) taken)))))))


; end matches
;--------------------------------------------------

;chap 7

(mac setnil (var) (list '= var nil))

(mac setnil (var) `(= ,var nil))

(mac nif (expr pos zero neg)
  `(if (> ,expr 0) ,pos
       (is ,expr 0) ,zero
       ,neg))

(mac nif (expr pos zero neg)
  (list 'if (list '> expr 0) pos
	    (list 'is expr 0) zero
	    neg))

(def greet (name)
  `(hello ,name))

(def f1 () 'toto)
(mac m1 () '((fn () 'toto)))
(mac m2 () '(pr 'toto))


(mac our-dolist ((var l (o result nil)) . body)
  `(do
     (map (fn (,var) ,@body)
	  ,l)
     (let ,var nil
       ,result)))

(mac when-bind ((var expr) . body)
  `(let ,var ,expr
     (when ,var
       ,@body)))

(mac cl-do (bindforms (test (o result nil)) . body)
  (w/uniq label
    `(loop
       ,(make-initforms bindforms)
       test
       ,(make-stepforms bindforms)
       ,@body)))
(def make-initforms (bindforms)
  (map
    (fn (b)
      (if (acons b)
	  (list (car b) (b 1))
	  (list b nil)))
    bindforms))
(def make-stepforms (bindforms)
  (map 
    (fn (b)
      (if (and (acons b) (b 2))
	  (list (car b) (b 2))
	  nil))
    bindforms))

;; (cl-do
;;        ((a 0 (++ a))
;; 	(b 1 ([= _ (+ 2 _)] b)))
;;        ((< a 10))
;;        (pr a)
;;        (pr b))



(mac our-and args
  (case (len args)
    0 t
    1 (car args)
      `(if ,(car args)
	   (our-and ,@(cdr args)))))

(mac our-andb args
  (if (no args)
      t
      (w/uniq (gf gp)
      `((rfn ,gf (,gp) ;ou bien rfn
	  (if (cdr ,gp)
	      (if (car ,gp)
		  (,gf (cdr ,gp)))
	    (car ,gp)))
	  (list ,@args)))))

(mac our-andb2 args
  (if (no args)
      t
      (let self 
	  (fn (rest)
	    (if (cdr rest)
		`(if ,(car rest)
		     ,(self (cdr rest)))
		(car rest)))
	(self args))))



;; (mac bidon args
;;   `(pr (list ,@args)))

(mac bidon args
  (afn (rest)
    (pr (car rest))
    args))

;chap 8

(mac with-redraw ((var objs) . body)
  (w/uniq (gob boxbefore)
    `(let ,gob ,objs
       (= ,boxbefore (bounds ,gob))
       (each ,var ,gob ,@body)
       (= boxafter (bounds ,gob))
       (redraw (boxunion ,boxbefore boxafter)))))

(def move-objs (objs dx dy)
  (with-redraw (o objs)
     (++ (obj-x o) dx)
     (++ (obj-y o) dy)))

(def scale-objs (objs factor)
  (with-redraw (o objs)
     (zap * (obj-x o) factor)
     (zap * (obj-y o) factor)))


;chap 9
;chap 10

(mac nthd (n l)
  `(nth-fn ,n ,l))
(def nth-fn (n l)
  (if (is n 0)
      (car l)
      (nth-fn (- n 1) (cdr l))))

(mac nthe (n l)
  `((rfn nth-fn (nn ll)
      (if (is nn 0)
	  (car ll)
	  (nth-fn (- nn 1) (cdr ll))))
    ,n ,l))

(mac ora args
  (or-expand args))
(def or-expand (args)
  (if (no args)
      nil
      (w/uniq s
	`(let ,s ,(car args)
	   (if ,s
	       ,s
	       ,(or-expand (cdr args)))))))

(mac orb args
  (if (no args)
      nil
      (w/uniq s
	`(let ,s ,(car args)
	   (if ,s
	       ,s
	       (orb ,@(cdr args)))))))


;chap 11

;fig 11.3

(def remove-duplicates (l)
  ((afn (xs acc)
     (if (no xs)              (rev acc)
	 (find (car xs) acc)  (self (cdr xs) acc)
	                      (self (cdr xs) (cons (car xs) acc))))
   l nil))

(def insert-after-every (e xs)
  (if (no xs)
      nil
      (cons (car xs) (cons nil (insert-after-every e (cdr xs))))))

(mac condlet (clauses . body)
  (w/uniq bodfn
    (let vars (map [cons _ (uniq)]
		   (remove-duplicates (map car (mappend cdr clauses))))
      `(let ,bodfn (fn ,(map car vars) ,@body)
	 (if ,@(mappend [condlet-clause vars _ bodfn]
		    clauses))))))

;; (mac condlet (clauses . body)
;;   (w/uniq bodfn
;;     (let vars (map [cons _ (uniq)]
;; 		   (remove-duplicates (map car (mappend cdr clauses))))
;;       `(pr vars))))

(def condlet-clause (vars cl bodfn)
  `(,(car cl) (with ,(insert-after-every nil (map cdr vars))
		(= ,@(condlet-binds vars cl))
		(,bodfn ,@(map cdr vars)))))

(def condlet-binds (vars cl)
  (mappend [if (acons _)
	       (cons (cdr (assoc (car _) vars))
		     (cdr _))]
	   (cdr cl)))

      

;11.4
(mac w/db (db . body)
  (w/uniq temp
    `(let ,temp *db*
       (unwind-protect ;atomic ?
	 (do
	   (= *db* ,db)
	   (lock *db*)
	   ,@body)
	 (do
	   (release *db*)
	   (= *db* ,temp))))))

(mac if3 (test t-case nil-case ?-case)
  `(case ,test
     (nil) ,nil-case
     ?     ?-case
     t     t-case))

(mac nif (expr pos zero neg)
  (w/uniq g
    `(let ,g ,expr
       (if (> 0 ,g)   ,pos
	   (is 0 ,g)  ,zero
	    ,neg))))
	   

;11.6
(mac in (obj . choices)
  (w/uniq insym
    `(let ,insym ,obj
       (or ,@(map (fn (c) `(is ,insym ,c)) choices)))))

(mac inq (obj . args)
  `(in ,obj ,@(map (fn (a) `',a) args)))

(mac in-if (f . choices)
  (w/uniq fnsym
    `(let ,fnsym ,f
       (or ,@(map (fn (c) `(,fnsym ,c)) choices)))))

(mac >case (expr . clauses)
  (w/uniq g
    `(let ,g ,expr
       (if @(mappend [casex g _] clauses)))))

(def >casex (g cl)
  (with (key (car cl) rest (cdr cl))
    (if (acons key)  '((in ,g ,key) ,@rest)
	(inq key t otherwise) ,@rest
        (error "bad >case clause"))))

(mac do-tuples/o (parms source . body)
  (if parms
      (w/uniq src
	`(let ,src ,source
	   (map (fn ,parms ,@body)
		,@(map0-n (fn (n) `(nthcdr ,n ,src)) (- (len parms) 1)))))))


(mac do-tuples/c (parms source . body)
  (if parms
      (w/uniq (src rest bodfn)
	(let np (len parms)
	  `(let ,src ,source
	     (when (nthcdr ,(- np 1) ,src)
	       (let ,bodfn (fn ,parms ,@body)
		 (loop (= ,rest ,src) 
		       (nthcdr ,(- np 1) ,rest) 
		       (= ,rest (cdr ,rest))
		       (,bodfn ,@(map1-n (fn (n) `(,rest ,(- n 1))) np)))
		 ,@(map (fn (args) `(,bodfn ,@args))
			(dt-args np rest src))))
	     nil)))))

(def dt-args (np rest src)
  (map0-n (fn (m) 
	    (map1-n (fn (n)
		      (let x (+ m n)
			(if (>= x np)
			    `(,src ,(- x np))
			    `(,rest ,(- x 1)))))
		    np))
	  (- np 2)))
		    
;chap 12

;12.1
(mac allf (val . args)
  (w/uniq gval
    `(let ,gval ,val
       (= ,@(mappend [list _ gval] args)))))

(mac nilf args `(allf nil ,@args))

(mac tf args `(allf t ,@args))

(mac toggle args
  `(do
     ,@(map [`(toggle2 _)] args)))

(mac toggle args
  `(do
     ,@(map (fn (x) `(toggle2 x)) args)))

(mac toggle2 (v)   ; faux!!!!
  (w/uniq gv
    `(let ,gv ,v
       (= ,v (no ,gv)))))

(mac toggle2 (v)
  `(zap no ,v)) 

;12.2
(mac zappend args      ; = ++
  `(zap join ,@args))

(mac zappend1 (l obj)              ;cf p 174
  `(zap join ,l (list ,obj)))

(mac zappendnew (l obj)
  `(zap (fn (place obj)
	  (unless (mem obj place)
	    (join place (list obj))))
	,l
	,obj))

;12.3
(mac popn (n place)
  (w/uniq (gn gl)
    (let (binds val setter) (setforms place)
      `(atwiths ,(+ binds (list gn n gl val))
		(do1 (firstn ,gn ,gl)
		     (,setter (nthcdr ,gn ,gl)))))))

;12.4

;; (mac defr (f args rf)
;;   `(def f args
;;        (if no xs
;; 	   nil
;; 	   (rf f args))))

;; (defr copylist (xs) 
;;       [cons (car _) (

(def mapcon (f xs)
  (if (no xs)
      nil
      (+ (f xs) (mapcon f (cdr xs)))))

(def maplist (f xs)
  (if (no xs)
      nil
      (cons (f xs) (maplist f (cdr xs)))))

(mac sortf (op . places)
  (with (meths (map setforms places)
	 temps (n-of (len places) (uniq)))
    `(withs ,(+ (mappend [_ 0] meths)
	       (mappend (fn (m t) (list t (m 1))) meths temps))
       ,@(mapcon
	   (fn 
	     (rest)
	     (map
	       (fn (arg) `(unless (,op ,(car rest) ,arg)
				(swap ,(car rest) ,arg)))
	       (cdr rest)))
	   temps)
       ,@(map (fn (m t) `(,(m 2) ,t)) meths temps))))

(= *cache* (table))

(def retrieve(key)
  (aif (*cache* key)
       it
       (cdr (assoc key *world*))))

(defset retrieve (key)
  (w/uniq g
    (list (list g key)
	  `(retrieve ,g)
	  `(fn (val) (= (*cache* ,key) val)))))
    

;chap 13

;cf avg

(mac avg ns
  `(/ (+ ,@args) ,(len args)))

(def most-of args
  (with (all  0
	 hits 0)
    (each a args
      (++ all)
      (if a (++ hits)))
    (> hits (/ all 2))))

(mac most-of args
  (w/uniq hits
    (let need (floor (/ (len args) 2))
      `(let ,hits 0
	 (or ,@(map (fn (a) `(and ,a (> (++ ,hits) ,need)))
		    args))))))

(def nthmost (n l)
  ((sort > l) n))

(mac nthmost (n l)
  (if (and (number n) (< n 20))
      (w/uniq (gl gi)
	(let syms (map0-n [uniq] n)
	  `(let ,gl ,l
	     (unless (< (len ,gl) ,(+ 1 n))
	       ,@(gen-start gl syms)
	       (each ,gi ,gl
		 ,(nthmost-gen gi syms t))
	       ,(last syms)))))
      `((sort > l) n)))

(def gen-start (gl syms)
  (rev
    (maplist
	(fn (syms)
	  (w/uniq var
	    `(let ,var (pop ,gl)
	       ,(nthmost-gen var (rev syms)))))
	(rev syms))))

(def nthmost-gen (var vars (o long? nil))
  (if (no vars)
      nil
      (let else (nthmost-gen var (cdr vars) long?)
	(if (and (no long?) (no else))
	    `(= ,(car vars) ,var)
	    `(if (> ,var ,(car vars))
		 (= ,@(mappend list
			       (rev vars)
			       (cdr (rev vars)))
		    ,(car vars) ,var)
		 ,else)))))


(= *segs* 20)
(= *du* (/ 1.0 *segs*))
(= *pts* nil)

(mac genbez (x0 y0 x1 y1 x2 y2 x3 y3)
  (w/uniq (gx0 gx1 gy0 gy1 gx3 gy3)
    `(withs (,gx0 ,x0 ,gy0 ,y0
	     ,gx1 ,x1 ,gy1 ,y1
	     ,gx3 ,x3 ,gy3 ,y3
	     cx (* (- ,gx1 ,gx0) 3)
	     cy (* (- ,gy1 ,gy0) 3)
	     px (* (- ,x2 ,gx1) 3)
	     py (* (- ,y2 ,gy1) 3)
	     bx (- px cx)
	     by (- py cy)
	     ax (- ,gx3 px ,gx0)
	     ay (- ,gy3 py ,gy0))
       (= ((*pts* 0) 0) ,gx0
	  ((*pts* 0) 0) ,gy0)
       ,@(map1-n (fn (n) 
		   (withs (u (* n *du*)
			   u^2 (* u u)
			   u^3 (* u u^2))
		     `(= ((*pts* ,n) 0)
			 (+ (* ax ,u^3)
			    (* bx ,u^2)
			    (* cx ,u)
			    ,gx0)
			 ((*pts* ,n) 1)
			 (+ (* ay ,u^3)
			    (* by ,u^2)
			    (* cy ,u)
			    ,gy0))))
		 (- *segs* 1))
       (= ((*pts* *segs*) 0) ,gx3
	  ((*pts* *segs*) 1) ,gy3))))
		 
;chap 14

(mac awhile (expr . body)
  `(let it nil
     (while ((fn (e) (= it e) it) ,expr)
	    ,@body)))

	
;chap 15

(mac olfn (expr)
  `(,@(rbuild expr)))

(def rbuild (expr)
  (if (or (atom expr) (is (car expr) 'fn)) expr
      (is (car expr) 'compose)             (build-compose (cdr expr))
                                           (build-call (car expr) (cdr expr))))

(def build-call (op fns)
  (w/uniq g
    `(fn (,g)
       (,op ,@(map (fn (f) `(,(rbuild f) ,g))
		   fns)))))

(def build-compose (fns)
  (w/uniq g
    `(fn (,g)
       ,((afn (fns)
	  (if fns
	      `(,(rbuild (car fns)) ,(self (cdr fns)))
	      g))
	  fns))))

(mac alrec (rec (o base nil))
  (w/uniq gfn
    `(lrec (fn (it ,gfn)
	     (let rec (fn () (,gfn))
	       ,rec))
	   ,base)))

;symbol macros in arc?

(mac on-cdrs (rec base . lsts)
  `(alrec ,rec (fn () ,base) ,@lsts))

(def our-copy-list (l)
  (on-cdrs (cons it (rec)) nil l))

(def our-remove-duplicate (l)
  (on-cdrs (adjoin it (rec)) nil l))

(def our-find-if (f l)
  (on-cdrs (if (f it) it (rec)) nil l))

(def our-some (f l)
  (on-cdrs (or (f it) (rec)) nil l))
;some and find-if defined using more specific reclist

(def unions sets
  (on-cdrs (union it (rec)) (car sets) (cdr sets)))

(def intersection (xs ys)
  (rem (fn (y) (no:some y xs))
       ys))

(def intersections sets
  (unless (some no sets)
    (on-cdrs (intersection it (rec)) (car sets) (cdr sets))))

(def set-difference (xs ys)
  (rem (fn (x) (some x ys))
       xs))

(def differences (s . outs)
  (on-cdrs (set-difference (rec) it) s outs))

(def maxmin (args)
  (when args
    (on-cdrs (withs (l (rec) mx (car l) mn (cadr l))
	       (list (max mx it) (min mn it)))
	     (list (car args) (car args))
	     (cdr args))))
;15.3

;fig 15.5
;is there something like symbol macros in arc?

;"Because macros are first-class objects, there is no need for Common 
;Lisp's macrolet. You can give a macro local scope with let, just as 
;you would give a value to any other variable."
;http://www.paulgraham.com/arcll1.html


(mac atrec (rec (o base 'it))
  (w/uniq (lfn rfn)
    `(trec (fn (it ,lfn ,rfn)
	     (withs (left (fn () (,lfn))
		     right (fn () (,rfn)))
	       ,rec))
	   (fn (it) ,base))))

(mac on-trees (rec base . trees)
  `((atrec ,rec ,base) ,@trees))
    
;see ontree, treewise

(= unforced (uniq))

(def delay-p (x)
  (and (alist x) (is (car x) 'delay)))

(mac delay (expr)
  (w/uniq self
    `(let ,self (list 'delay unforced nil)
       (= (,self 2)
	  (fn () (= (cadr ,self) ,expr)))
       ,self)))

(def force (x)
  (if (delay-p x)
      (if (is (cadr x) unforced)
	  ((x 2))
	  (cadr x))
      x))

;chap 16
;fig 16.1

(mac abbrev (short long)
  `(mac ,short args
     `(,',long ,@args)))

(abbrev zza and)

(mac abbrevs names
  `(do
     ,@(map (fn (pair) `(abbrev ,@pair))
	    (group names 2))))

;symbol properties in arc?

(mac a+ args
  (a+expand args nil))

(def a+expand (args syms)
  (if args
      (w/uniq symbol
	`(withs (,symbol ,(car args)
		 it ,symbol)
	   ,(a+expand (cdr args)
		      (+ syms (list symbol)))))
      `(+ ,@syms)))

(def mass-cost (menu-price)
  (a+ menu-price (* it .05) (* it 3)))