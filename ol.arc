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
;;         (a 
;;           (rev  
;;             (accum b
;;               (each taken (range 1 3)
;;                 (aif (apply-move l line taken)
;;                      (b it))))))))
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
;;         (b 1 ([= _ (+ 2 _)] b)))
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
;;                    (remove-duplicates (map car (mappend cdr clauses))))
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
;;            nil
;;            (rf f args))))

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

(mac analist args
  (alist-expand args nil))

(def alist-expand (args syms)
  (if args
      (w/uniq symbol
        `(withs (,symbol ,(car args)
                 it ,symbol)
           ,(alist-expand (cdr args) 
                          (+ syms (list symbol)))))
      `(list ,@syms)))

;fig 16.4
(mac defanaph (name (o calls nil))
  (let calls (or calls (pop-symbol name))
    `(mac ,name args
       (anaphex args (list ',calls)))))

(def anaphex (args expr)
  (if args
      (w/uniq symb
        `(withs (,symb ,(car args)
                 it ,symb)
           ,(anaphex (cdr args)
                     (+ expr (list symb)))))
      expr))

(def pop-symbol (symb)
  (sym (cut (string symb) 1)))

;no read macro in arc

;chap 18 

; fig 18.1

(mac dbind (pat seq . body)
  (w/uniq gseq
    `(let ,gseq ,seq
       ,(dbind-ex (destruc pat gseq atom) body))))

(def destruc (pat seq (o atom? atom) (o n 0))
  (if (no pat)
      nil
      (if (atom? pat)
          `((,pat (cut ,seq ,n)))
          (withs (p (car pat)
                    rec (destruc (cdr pat) seq atom? (+ 1 n)))
            (if (atom? p)
                (cons `(,p (,seq ,n))
                      rec)
                (w/uniq var
                  (cons (cons `(,var (,seq ,n))
                              (destruc p var atom?))
                        rec)))))))

(def dbind-ex (binds body)
  (if (no binds)
      `(do ,@body)
      `(withs ,(mappend (fn (b) 
                    (if (acons (car b))
                        (car b)
                        b))
                  binds)
         ,(dbind-ex (mappend (fn (b) 
                               (if (acons (car b))
                                   (cdr b)))
                             binds)
                    body))))

;no array, matrix or structure in arc

;; ;fig 18.4
;; ;TODO: implement symbol macros

;; (mac w/places (pat seq . body)
;;   (w/uniq gseq
;;     `(let ,gseq ,seq
;;        (wplac-ex (binds body)))))

;; (def wplac-ex (binds body)
;;   (if (no binds)
;;       `(do ,@body)
;;       (

;fig 18.5

;convention: t means "matches with no binding"
;see if annoying to have t in assoc list (not until now)
(def match (x y (o binds nil))
  (aif
    (or (is x y) (is x '_) (is y '_)) (or binds t)
    (binding x binds) (match (cdr it) y binds)
    (binding y binds) (match x (cdr it) binds)
    (varsym? x) (cons (cons x y) binds)
    (varsym? y) (cons (cons y x) binds)
    (and (acons x)(acons y)(match (car x) (car y) binds))
        (match (cdr x) (cdr y) it)
     nil))

;(match '(p a b c a) '(p ?x ?y c ?x))
;((?y . b) (?x . a) . t)
;; arc> (match '(p ?x b ?y a) '(p ?y b c a))
;; ((?y . c) (?x . ?y) . t)

(def varsym? (x)
  (and x (isa x 'sym) (is ((string x) 0) #\?)))

(def binding (x binds)
  ((afn (x binds)
    (aif (assoc x binds)
         (or (self (cdr it) binds)
             it)))
   x binds))
;the book's version returns (values (cdr b) b) we just return b because
; (cdr b) can be nil

;; arc> (binding '?x '((?y . c) (?x . ?y) . t))
;; (?y . c)



; pattern matching version of dbind
(mac if-match (pat seq then (o else nil))
  `(aif (match ',pat ,seq)
        (withs ,(mappend (fn (v) `(,v (cdr:binding ',v it)))
                   (vars-in then atom))
            ,then)
        ,else))


(def vars-in (expr (o atom? atom))
  (if (atom? expr)
      (if (var? expr)(list expr) nil)
      (union is
             (vars-in (car expr) atom?)
             (vars-in (cdr expr) atom?))))

(def var? (x)
  (and x (isa x 'sym) (is ((string x) 0) #\?)))

(mac if-match (pat seq then (o else nil))
  `(withs ,(mappend (fn (v) `(,v ',(uniq)))
                    (vars-in pat simple?))
     (pat-match ,pat ,seq ,then ,else)))

(mac pat-match (pat seq then else)
  (if (simple? pat)
      (match1 `((,pat ,seq)) then else)
      (w/uniq (gseq gelse)
        `(let ,gelse (fn () ,else)
           ,(gen-match (cons (list gseq seq)
                             (destruc pat gseq simple?))
                       then
                       `(,gelse))))))

(def simple? (x)
  (or (atom x) (is (car x) 'quote)))

(def gen-match (refs then else)
  (if (no refs)
      then
      (let then (gen-match (cdr refs) then else)
        (if (simple? (caar refs))
            (match1 refs then else)
            (gen-match (car refs) then else)))))

(def match1 (refs then else)
  (dbind ((pat expr) . rest) refs
    (if (uniq? pat)
          `(let ,pat ,expr
             (if (and (seq? ,pat)
                      ,(length-test pat rest))
                 ,then
                 ,else))
        (is pat'_) then
        (var? pat)
          (w/uniq ge
            `(let ,ge ,expr
               (if (or (uniq? ,pat) (iso ,pat ,ge))
                   (let ,pat ,ge ,then)
                   ,else)))
          `(if (iso ,pat ,expr) ,then ,else))))

(def seq? (x)
  (or (alist x) (isa x 'table) (isa x 'string)))

(def uniq? (s)
  (and s (isa s 'sym) (no (is s (sym (string s))))))

(def cdar (x)
  (cdr:car x))

;! last is different in arc and in common lisp
(def length-test (pat rest)
  (let fin (caar:cdr:last rest)
    (if (acons fin)
        `(is (len ,pat) ,(len rest))
        `(> (len ,pat) ,(- (len rest) 2)))))

; code for debug
;TODO rename prf is taken for print format
;; (def prf (f name)
;;   (fn args
;;     (let res nil
;;       (prn name args)
;;       (= res (apply f args))
;;       (prn name " <-- " res)
;;       res)))

;; (mac prfn (f)
;;   `(= ,f (prf ,f ',f)))

(def abab (seq)
  (if-match (?x ?y ?x ?y) seq
            (list ?x ?y)
            nil))

;chap 19
(def make-db ()
  (table))

(= default-db* (make-db))

(def clear-db ((o db default-db*))
  (= db (table)))

(mac db-query (key (o db 'default-db*))
  `(,db ,key))

(def db-push (key val (o db default-db*))
  (push val (db key)))

(mac fact (pred . args)
  `(do
     (db-push ',pred ',args)
     ',args))

;edible = eatable

;; mapcan
;; Function arguments:
;;   (function list &rest more-lists)
;; Function documentation:
;;   Applies fn to successive elements of list, returns NCONC of results.
;; Its declared argument types are:
;;   ((OR FUNCTION SYMBOL) LIST &REST LIST)
;; Its result type is:
;;   LIST

(def lookup (pred args (o binds nil))
  (mappend (fn (x)
             (aif (match x args binds) (list it)))
           (db-query pred)))

;dolist
;; dolist binds a variable to the elements of a list in order and stops 
;; when it hits the end of the list.

;;     > (dolist (x '(a b c)) (print x))
;;     A 
;;     B 
;;     C 
;;     NIL 



(mac w/answer (query . body)
  (w/uniq binds
    `(each ,binds (interpret-query ',query)
       (withs ,(mappend (fn (v)
                      `(,v (cdr:binding ',v ,binds)))
                    (vars-in query atom))
         ,@body))))

(def interpret-query (expr (o binds nil))
  (case (car expr)
    and   (interpret-and (rev:cdr expr) binds)
    or    (interpret-or  (cdr expr) binds)
    not   (interpret-not (cadr expr) binds)
          (lookup (car expr) (cdr expr) binds)))

(def interpret-and (clauses binds)
  (if (no clauses)
      (list binds)
      (mappend (fn (b)
                 (interpret-query (car clauses) b))
               (interpret-and (cdr clauses) binds))))

(def interpret-or (clauses binds)
  (mappend (fn (c)
             (interpret-query c binds))
           clauses))

(def interpret-not (clause binds)
  (if (interpret-query clause binds)
      nil
      (list binds)))

(clear-db)
(fact painter hogarth william english)
(fact painter canale antonio venetian)
(fact painter reynolds joshua english)
(fact dates hogarth 1697 1772)
(fact dates canale 1697 1768)
(fact dates reynolds 1723 1792)

(mac w/answer (query . body)
  `(w/uniq ,(vars-in query simple?)
     ,(compile-query query `(do ,@body))))

(def compile-query (q body)
  (case (car q)
    and  (compile-and (cdr q) body)
    or   (compile-or  (cdr q) body)
    not  (compile-not (cadr q) body)
    lisp `(if ,(cadr q) ,body)
         (compile-simple q body)))

(def compile-simple (q body)
  (w/uniq fact
    `(each ,fact (db-query ',(car q))
         (pat-match ,(cdr q) ,fact ,body nil))))

(def compile-and (clauses body)
  (if (no clauses)
      body
      (compile-query (car clauses)
                     (compile-and (cdr clauses) body))))

(def compile-or (clauses body)
  (if (no clauses)
      nil
      (w/uniq gbod
        (let vars (vars-in body simple?)
          `(let ,gbod (fn ,vars ,body)
                ,@(map (fn (cl)
                         (compile-query cl `(,gbod ,@vars)))
                       clauses))))))

;block
;http://www.lispworks.com/documentation/HyperSpec/Body/s_block.htm
;; The special operators *block* and *return-from* work together to provide a 
;; structured, lexical, non-local exit facility. 
;; At any point lexically contained within forms, return-from can be used with 
;; the given name to return control and values from the block form, except 
;; when an intervening block with the same name has been established, in which 
;; case the outer block is shadowed by the inner one.


(def compile-not (q body)
  (w/uniq tag
    `(let ,tag nil
          ,(compile-query q `(= ,tag t))
          (if (no ,tag)
              ,body))))

;chap 20

(def dft (tree)
  (if (no tree)          nil
      (no (acons tree))  (pr tree)
                         (do (dft:car tree)
                             (dft:cdr tree))))

(= saved* nil)

;; (def dft-node (tree)
;;   (if (no tree)         (restart)
;;       (no (acons tree)) tree
;;                         (ccc
;;                           (fn (c)
;;                             (= saved*
;;                                (cons (fn ()
;;                                        (c (dft-node (cdr tree))))
;;                                      saved*))
;;                             (dft-node (car tree))))))

;; (def restart ()
;;   (if (no saved*)
;;       'done
;;       (let cont (car saved*)
;;         (= saved* (cdr saved*))
;;         (cont))))

;; (def dft2 (tree)
;;   (= saved* nil)
;;   (let node (dft-node tree)
;;     (if (is node 'done) nil
;;                         (do (pr node)
;;                             (restart)))))


; with this code, without continuation, dft2 does not work
;; (def dft-node (tree)
;;   (if (no tree)         (restart)
;;       (no (acons tree)) tree
;;                         (do
;;                           (= saved*
;;                              (cons
;;                                (fn ()
;;                                  (dft-node (cdr tree)))
;;                                saved*))
;;                         (dft-node (car tree)))))

;(= t1 '(a (b (d h)) (c e (f i) g)))
;(= t2 '(1 (2 (3 6 7) 4 5)))

;http://www.thefreedictionary.com/shaft
;shaft 8.  A long, narrow, often vertical passage sunk into the earth,
;as for mining ore; a tunnel.

(= cont* idfn)

(mac =fn (parms . body)
  `(fn (cont* ,@parms) ,@body))


; ,,@ does not work with parms = nil (unquote take exactly one arg)
(mac =def (name parms . body)
  (let f (sym (+ "=" (string name)))
    `(do
       (mac ,name ,parms
         (list ',f 'cont* ,@parms))
       (def ,f (cont* ,@parms) ,@body))))


(mac =bind (parms expr . body)
  `(let cont* (fn ,parms ,@body) ,expr))
;defines the continuation with the body before to pass it to expr

(mac =values retvals
  `(cont* ,@retvals))

(mac =fncall (f . args)
  '(,fn cont* ,@args))

(mac =apply (f . args)
  `(apply ,f cont* ,@args))

;the same definition works in REPL, and not in ol.arc
(=def dft-node (tree)
  (if (no tree)         (restart)
      (no (acons tree)) (=values tree)
                        (do
                          (push (fn () (dft-node (cdr tree)))
                              saved*)
                          (dft-node (car tree)))))

(=def restart ()
  (if saved*
      ((pop saved*))
      (=values 'done)))

(=def dft2 (tree)
  (= saved* nil)
  (=bind (node) (dft-node tree)
    (if (is node 'done)
        (=values nil)
        (do (pr node)
            (restart)))))

;this example helped me to understand mapticks in Peter Seibel's
;with-gensyms
;; * (let ((n '(a b)))
;;     (mapticks `(,n (gensym (string ,n))) n))
;; ((A (GENSYM (STRING A))) (B (GENSYM (STRING B))))

;; * (macroexpand-1 '(mapticks `(,n (gensym (string ,n))) n))
;; (MAPCAR (LAMBDA (N) `(,N (GENSYM (STRING ,N)))) N)
;; T

;chap 21
(= procs* nil)
(= proc* nil)
(= halt* (uniq))


(= default-proc*
   (list 'proc
         nil
         (fn (x)
	   (pr ">> ")
           (prn (eval (read)))
           (pick-process))
         nil))

(mac fork (expr pri)
  `(do1 ',expr
        (push (list 'proc
                    ,pri
                    (fn (,(uniq))
                      ,expr
                      (pick-process))
                    nil)
              procs*)))

;catch is implemented by creating a context, but eval ignore any context,
;so throw is undefined. Use a global continuation instead.
(mac program (name args . body)
  `(def ,name ,args
     (= procs* nil)
     ,@body
     (ccc
       (fn (c)
	 (= halt* c)
	 (while t (pick-process))))))

;; * (describe 'catch)
;; CATCH is an external symbol in the COMMON-LISP package.
;; Special form documentation:
;;   Catch Tag Form*
;;   Evaluates Tag and instantiates it as a catcher while the body forms are
;;   evaluated in an implicit PROGN.
;;   If a THROW is done to Tag within the dynamic
;;   scope of the body, then control will be transferred to the end of the body
;;   and the thrown values will be returned.

(def pick-process ()
  (let (p val) (most-urgent-process)
       (= proc* p
	  procs* (rem p procs*))
       ((p 2) val)))

(def most-urgent-process ()
  (withs (proc1 default-proc*
	  max   -1
	  val1  t)
    (each p procs*
      (let pri (p 1)
	(if (> pri max)
	    (let val (or (no (p 3))
			 ((p 3)))
	      (when val
		(= proc1 p
		   max   pri
		   val1  val))))))
    (list proc1 val1)))

(def arbitrator (test cont)
  (= (proc* 2) cont
     (proc* 3) test)
  (push proc* procs*)
  (pick-process))

;; (mac wait (parm test . body)
;;   `(arbitrator (fn () ,test)
;;	       (fn (,parm) ,@body)))

(mac wait (test)
  `(ccc
     (fn (c)
       (arbitrator (fn () ,test)
		   c))))
;; (mac yield body
;;   `(arbitrator nil (fn (,(uniq)) ,@body)))

(def yield ()
  (ccc
    (fn (c)
      (arbitrator nil c))))

(def setpri (n)
  (= (proc* 1) n))

(def halt ()
  (halt* nil))

(def kill ((o obj nil))
  (if obj
      (= procs* (rem obj procs*))
      (pick-process)))

;to loot : to steal, especially as part of war, riot or other group violence.
;to plunder : (transitive) To pillage, take or destroy all the goods of,
; by force (as in war); to raid, sack.
;to ransom : To pay a price to set someone free from captivity or punishment.

(= open-doors* nil)
(def pedestrian ()
  (prn (wait (car open-doors*))))
(program ped ()
  (fork (pedestrian) 1))

(= bboard* nil)
(def claim f
  (push f bboard*))
(def unclaim f
  (pull [iso _ f] bboard*))
(def check f
  (find [iso _ f] bboard*))

(def visitor (door)
  (pr "Approach ")
  (prn door)
  (claim 'knock door)
  (wait (check 'open door))
  (pr "Enter ")
  (prn door)
  (unclaim 'knock door)
  (claim 'inside door))

(def host (door)
  (wait (check 'knock door))
  (pr "Open ")
  (prn door)
  (claim 'open door)
  (wait (check 'inside door))
  (pr "Close ")
  (prn door)
  (unclaim 'open door))

(program ballet ()
  (fork (visitor 'door1) 1)
  (fork (host 'door1) 1)
  (fork (visitor 'door2) 1)
  (fork (host 'door2) 1))

(def capture (city)
  (take city)
  (setpri 1)
  (yield)
  (fortify city))

(def plunder (city)
  (loot city)
  (ransom city))

(def  take (c) (prf "Liberating ~A \n\n" c))
(def fortify (c) (prf "Rebuilding ~A \n\n" c))
(def loot (c) (pr "Nationalizing ") (prn c))
(def ransom (c) (pr "Refinancing ") (prn c))

(program barbarians ()
  (fork (capture 'rome) 100)
  (fork (plunder 'rome) 98))

;chap22

(= paths* nil)
(= failsym '@)

(def choose (choices)
  (if (no choices)
      (fail)
      (ccc
        (fn (c) 
          (= paths* 
             (cons (fn () (c (choose (cdr choices))))
                   paths*))
          (car choices)))))

(def choosex choices
  (if (no choices)
      (fail)
      (ccc
        (fn (c) 
          (= paths* 
             (cons (fn () (c (apply choosex (cdr choices))))
                   paths*))
          (car choices)))))

(mac choosemac choices
  (if (no choices)
      '(fail)
      `(do
         (ccc
           (fn (c)
             (= paths* 
                (cons (fn () (c (choosemac ,@(cdr choices))))
                      paths*))
           ,(car choices))))))

(def deffail ()
  (ccc
    (fn (c)
      (= fail 
         (fn ()
           (if (no paths*)
               (c failsym)
               (let p1 (car paths*)
                 (= paths* (cdr paths*))
                 (p1))))))))

(ccc (fn (c) (= testfail (fn () (c failsym)))));same def in REPL works.
; the continuation of the reading of a file is not a good one.

;; (def fail ()
;;   (if paths*
;;       (let p1 (car paths*)
;;         (= paths* (cdr paths*))
;;         (p1))
;;       failsym))

(def two-numbers ()
  (list (choose '(0 1 2 3 4 5))
        (choose '(0 1 2 3 4 5))))
(def parlor-trick (n)
  (let nums (two-numbers)
    (if (is (apply + nums) n)
        `(the sum of ,@nums)
        (fail))))

;dict: maze
;dict: hounded p299
(def mark ()
  (= paths* (cons fail paths*)))

(def prune ()
  (if (or (no paths*) (is (car paths*) fail))
      (= paths* (cdr paths*))
      (do (= paths* (cdr paths*))
          (prune))))

(def find-boxes()
  (= paths* nil)
  (let city (choose '(la ny bos))
    (mark)
    (prn)
    (withs (store (choose '(1 2))
	    box   (choose '(1 2))
	    triple (list city store box))
      (pr triple)
      (if (coin? triple)
	  (do (prune) (pr 'c)))
      (fail))))

(def coin? (x)
  (mem [iso _ x] '((la 1 2) (ny 1 1) (bos 2 2))))

(def kids (n)
  (case n
    a '(b c)
    b '(d e)
    c '(d f)
    f '(g)))

(def descent (n1 n2)
  (if (is n1 n2)
      (list n2)
      (let p (try-paths (kids n1) n2)
        (if p (cons n1 p) nil))))

(def try-paths (ns n2)
  (if (no ns)
      nil
      (or (descent (car ns) n2)
          (try-paths (cdr ns) n2))))

(def descent (n1 n2)
  (if (is n1 n2)     (list n2)
      (no (kids n1)) (fail)
                     (cons n1 (descent (choose (kids n1)) n2))))

;dico breadth

(def true-choose (choices)
  (ccc
    (fn (c)
      (= paths*
	 (append paths*
		 (map (fn (choice)
			(fn () (c choice)))
		      choices)))
      (fail))))

;chap 23

;dico spell
;dico intelligent-seeming

;fig 23.3

(mac defnode (name . arcs)
  `(def ,name (pos regs) (choosemac ,@arcs)))

(mac down (sub next . cmds)
  `(let (* pos regs) (,sub pos (cons nil regs))
     (,next pos ,(compile-cmds cmds))))

;; (mac cat (cat next . cmds)
;;   `(if (is (len sent*) pos)
;;        (fail)
;;        (let * (sent* pos)
;;          (if (mem ',cat (types *))
;;              (,next (+ 1 pos) ,(compile-cmds cmds))
;;              (fail)))))

; (fail) within a choose always returns @

(mac cat (cat next . cmds)
  `(if (is (len sent*) pos)
       (fail)
       (let * (sent* pos)
         (if (mem ',cat (types *))
             (,next (+ 1 pos) ,(compile-cmds cmds))
             (fail)))))

(mac jump (next . cmds)
  `(,next pos ,(compile-cmds cmds)))

(def compile-cmds (cmds)
  (if (no cmds)
      'regs
      `(,@(car cmds) ,(compile-cmds (cdr cmds)))))

(mac up (expr)
  `(let * (car:nthcdr pos sent*)
     (list ,expr pos (cdr regs))))

(mac getr (key (o regs 'regs))
  `(let result (cdr (assoc ',key (car ,regs)))
     (if (cdr result) result car result)))

(mac set-register (key val regs)
  `(cons (cons (cons ,key ,val) (car ,regs)) (cdr ,regs)))

(mac setr (key val regs)
  `(set-register ',key (list ,val) ,regs))

(mac pushr (key val regs)
  `(set-register ',key
                 (cons ,val (cdr (assoc ',key (car ,regs))))
                 ,regs))

;; (defnode s
;;    (cat noun s2
;;      (setr subj *)))

;; (defnode s2
;;    (cat verb s3
;;      (setr v *)))

;; (defnode s3
;;    (up `(sentence
;;            (subject ,(getr subj))
;;            (verb ,(getr v)))))

;; (defnode s
;;   (down np s/subj
;;     (setr mood 'decl)
;;     (setr subj *))
;;   (cat v v
;;     (setr mood 'imp)
;;     (setr subj '(np (pron you)))
;;     (setr v *)))

;fig 23.5
(mac w/parses (node sent . body)
  (w/uniq (pos regs)
   `(do
      (= sent* ,sent
         paths* nil)
      (let (parse ,pos ,regs) (,node 0 '(nil))
        (if (is ,pos (len sent*))
            (do ,@body (fail))
            (fail))))))

(def types (word)
  (if (mem word '(do does did))     '(aux v)
      (mem word '(time times))      '(n v)
      (mem word '(fly flies))       '(n v)
      (mem word '(like))            '(v prep)
      (mem word '(liked likes))     '(v)
      (mem word '(a an the))        '(det)
      (mem word '(arrow arrows))    '(n)
      (mem word '(i you he she him her it)) '(pron)))

(defnode mods
   (cat n mods/n
      (setr mods *)))

(defnode mods/n
   (cat n mods/n
      (pushr mods *))
   (up `(n-group ,(getr mods))))

;; ;fun exercise with continuations
;; (def lastcont()
;;   (let tmpc lastcont*
;;     (ccc
;;       (fn (c)
;;         (= lastcont* c)
;;         (tmpc nil)))))

(defnode np
  (cat det np/det
     (setr det *))
  (jump np/det
     (setr det nil))
  (cat pron pron
     (setr n *)))

(defnode pron
  (up `(np (pronoun ,(getr n)))))

(defnode np/det
  (down mods np/mods
    (setr mods *))
  (jump np/mods
    (setr mods nil)))

(defnode np/mods
  (cat n np/n
    (setr n *)))

(defnode np/n
  (up `(np (det ,(getr det))
           (modifiers ,(getr mods))
           (noun ,(getr n))))
  (down pp np/pp
    (setr pp *)))

(defnode np/pp
  (up `(np (det ,(getr det))
           (modifiers ,(getr mods))
           (noun ,(getr n))
           ,(getr pp))))

(defnode pp
  (cat prep pp/prep
    (setr prep *)))

(defnode pp/prep
  (down np pp/np
    (setr op *)))

(defnode pp/np
  (up `(pp (prep ,(getr prep))
           (obj ,(getr op)))))

(defnode s
  (down np s/subj
    (setr mood 'decl)
    (setr subj *))
  (cat v v
    (setr mood 'imp)
    (setr subj '(np (pron you)))
    (setr aux nil)
    (setr v *)))

(defnode s/subj
  (cat v v
    (setr aux nil)
    (setr v *)))

(defnode v
  (up `(s (mood ,(getr mood))
          (subj ,(getr subj))
          (vcl (aux ,(getr aux))
               (v ,(getr v)))))
  (down np s/obj
    (setr obj *)))

(defnode s/obj
  (up `(s (mood ,(getr mood))
          (subj ,(getr subj))
          (vcl (aux ,(getr aux))
               (v ,(getr v)))
          (obj ,(getr obj)))))

;chap 24

(mac w/inference_i (query . body)
  `(do
     (= paths* nil)
     (let binds (prove-query ',(rep_ query) nil)
	  (withs ,(mappend (fn (v) 
		       `(,v (fullbind ',v binds)))
		     (vars-in query))
	    ,@body
	    (fail)))))

(def rep_ (x)
  (if (atom x)
      (if (is x '_) (uniq "?") x)
      (cons (rep_ (car x)) (rep_ (cdr x)))))

(def fullbind (x b)
  (if (varsym? x) (aif (binding x b)
		       (fullbind (cdr it) b)
		       (uniq))
      (atom x) x
               (cons (fullbind (car x) b)
		     (fullbind (cdr x) b))))

(def prove-query (expr binds)
  (case (car expr)
    and  (prove-and (cdr expr) binds)
    or   (prove-or  (cdr expr) binds)
    not  (prove-not (cadr expr) binds)
         (prove-simple expr binds)))

(def prove-and (clauses binds)
  (if (no clauses)
      binds
      (let binds (prove-query (car clauses) binds)
	   (prove-and (cdr clauses) binds))))

(def prove-or (clauses binds)
  (let c (choose clauses)
    (prove-query c binds)))

(def prove-not (clauses binds)
  (let save-paths paths*
    (= paths* nil)
    (choosemac (let b (prove-query expr binds)
		    (= paths* save-paths)
		    (fail))
	       (do
		 (= paths* save-paths)
		 binds))))

(def prove-simple (query binds)
  (let r (choose rlist*)
    (implies r query binds)))

(= rlist* nil)

(mac <-i (con . ant)
  (let ant (if (is (len ant) 1)
	       (car ant)
	       `(and ,@ant))
    `(len (++ rlist* (list (rep_ (cons ',ant ',con)))))))

(def implies (r query binds)
  (let r2 (change-vars r)
    (aif (match query (cdr r2) binds)
	 (prove-query (car r2) it)
	 (fail))))

(def sublis (al tree)
  (treewise cons [aif (assoc _ al) (cdr it) _] tree))

(def change-vars (r)
  (sublis (map (fn (v) (cons v (uniq '?)))
	       (vars-in r))
	  r))

;dict to gaunt
;dict ravenously
;dict turpentine

(<-i (painter ?x) (hungry ?x) (smells-of ?x turpentine))
(<-i (hungry ?x) (or (gaunt ?x) (eats-ravenously ?x)))
(<-i (gaunt raoul))
(<-i (smells-of raoul turpentine))
(<-i (painter rubens))
(<-i (append nil ?xs ?xs))
(<-i (append (?x . ?xs) ?ys (?x . ?zs)) (append ?xs ?ys ?zs))

(mac w/inference (query . body)
  (withs (vars (vars-in query simple?)
          gb (uniq))
    `(w/uniq ,vars
       (= paths* nil)
       (let ,gb ,(gen-query (rep_ query))
         (withs ,(mappend (fn (v) `(,v (fullbind ,v ,gb)))
                          vars)
           ,@body)
         (fail)))))

(= varsym? uniq?)

(def gen-query (expr (o binds nil))
  (case (car expr)
    and (gen-and (cdr expr) binds)
    or  (gen-or  (cdr expr) binds)
    not (gen-not (cadr expr) binds)
        `(prove (list ',(car expr)
                      ,@(map pform (cdr expr)))
                ,binds)))

(def gen-and (clauses binds)
  (if (no clauses)
      binds
      (w/uniq gb
        `(let ,gb ,(gen-query (car clauses) binds)
           ,(gen-and (cdr clauses) gb)))))
(def gen-or (clauses binds)
  `(choosemac
     ,@(map (fn (c) (gen-query c binds))
            clauses)))
(def gen-not (expr binds)
  (w/uniq gpaths
    `(let ,gpaths paths*
       (= paths* nil)
       (choosemac
         (let b ,(gen-query expr binds)
           (= paths* ,gpaths)
           (fail))
         (do
           (= paths* ,gpaths)
           binds)))))

(def prove (query binds)
  (let r (choose rules*)
    (r query binds)))

(def pform (pat)
  (if (simple? pat)
      pat
      `(cons ,(pform (car pat)) ,(pform (cdr pat)))))

(= rules* nil)

(mac <- (con . ant)
  (let ant (if (is (len ant) 1)
               (car ant)
               `(and ,@ant))
    `(len (++ rules* (list ,(rule-fn (rep_ ant) (rep_ con)))))))

(def rule-fn (ant con)
  (w/uniq (val fact binds)
    `(fn (,fact ,binds)
       (w/uniq ,(vars-in (list ant con) simple?)
         (let ,val
             (match ,fact
                    (list ',(car con)
                          ,@(map pform (cdr con)))
                    ,binds)
           (if ,val
                 ,(gen-query ant val)
               (fail)))))))


(def rule-fn (ant con)
  (w/uniq (val fact binds paths)
    `(fn (,fact ,binds ,paths)
       (w/uniq ,(vars-in (list ant con) simple?)
         (let ,val
             (match ,fact
                    (list ',(car con)
                          ,@(map pform (cdr con)))
                    ,binds)
           (if ,val
                 ,(gen-query ant val paths)
               (fail)))))))

(mac w/inference (query . body)
  (w/uniq gb
    (let vars (vars-in query simple?)
      `(w/uniq ,vars
         (= paths* nil)
         (let ,gb ,(gen-query (rep_ query) nil 'paths*)
           (withs ,(mappend (fn (v) `(,v (fullbind ,v ,gb)))
                            vars)
             ,@body)
           (fail))))))

(def gen-query (expr binds paths)
  (case (car expr)
    and  (gen-and (cdr expr) binds paths)
    or   (gen-or  (cdr expr) binds paths)
    not  (gen-not (cadr expr) binds paths)
    lisp (gen-lisp (cadr expr) binds)
    is   (gen-is (cadr expr) (expr 2) binds)
    cut  `(do (= paths* ,paths)
	      ,binds)
         `(prove (list ',(car expr)
                       ,@(map pform (cdr expr)))
                 ,binds paths*)))

(def prove (query binds paths)
     (let r (choose rules*)
       (r query binds paths)))

(def gen-and (clauses binds paths)
  (if (no clauses)
      binds
      (w/uniq gb
        `(let ,gb ,(gen-query (car clauses) binds paths)
           ,(gen-and (cdr clauses) gb paths)))))
(def gen-or (clauses binds paths)
  `(choosemac
     ,@(map (fn (c) (gen-query c binds paths))
            clauses)))
(def gen-not (expr binds paths)
  (w/uniq gpaths
    `(let ,gpaths paths*
       (= paths* nil)
       (choosemac
         (let b ,(gen-query expr binds paths)
           (= paths* ,gpaths)
           (fail))
         (do
           (= paths* ,gpaths)
           binds)))))

(mac w/binds (binds expr)
  `(withs ,(mappend (fn (v) `(,v (fullbind ,v ,binds)))
                    (vars-in expr))
     ,expr))

(def gen-lisp (expr binds)
  `(if (w/binds ,binds ,expr)
       ,binds
       (fail)))

(def gen-is (expr1 expr2 binds)
  `(aif (match ,expr1 (w/binds ,binds ,expr2) ,binds)
        it
        (fail)))

(<- (painter ?x) (hungry ?x) (smells-of ?x 'turpentine))
(<- (hungry ?x) (or (gaunt ?x) (eats-ravenously ?x)))
(<- (gaunt 'raoul))
(<- (smells-of 'raoul 'turpentine))
(<- (painter 'rubens))

(<- (factorial 0 1))
(<- (factorial ?n ?f)
    (lisp (> ?n 0))
    (is ?n1 (- ?n 1))
    (factorial ?n1 ?f1)
    (is ?f (* ?n ?f1)))

(<- (append nil ?ys ?ys))
(<- (append (?x . ?xs) ?ys (?x . ?zs))
    (append ?xs ?ys ?zs))

(<- (quicksort (?x . ?xs) ?ys)
    (partition ?xs ?x ?littles ?bigs)
    (quicksort ?littles ?ls)
    (quicksort ?bigs ?bs)
    (append ?ls (?x . ?bs) ?ys))
(<- (quicksort nil nil))

(<- (partition (?x . ?xs) ?y (?x . ?ls) ?bs)
    (lisp (<= ?x ?y))
    (partition ?xs ?y ?ls ?bs))
(<- (partition (?x . ?xs) ?y ?ls (?x . ?bs))
    (lisp (> ?x ?y))
    (partition ?xs ?y ?ls ?bs))
(<- (partition nil ?y nil nil))

(<- (echo)
    (is ?x (read))
    (echo ?x))
(<- (echo 'done)
    (cut))
(<- (echo ?x)
    (lisp (do1 t (prn ?x)))
    (is ?y (read))
    (cut)
    (echo ?y))


;chap 25

;; (def rget (obj prop)
;;   (some [_ prop] (get-ancestors obj)))

;; (def get-ancestors (obj)
;;   (sort
;;     (fn (x y)(mem y (x 'parents)))
;;     (dedup
;;       ((afn (x)
;;          (++ (list x)
;;              (mappend self (x 'parents))))
;;        obj))))

;; (def obj parents
;;   (let obj (table)
;;     (= (obj 'parents) parents)
;;     (ancestors obj)
;;     obj))
;; (def ancestors (obj)
;;   (or (obj 'ancestors)
;;       (= (obj 'ancestors) (get-ancestors obj))))
;; (def rget (obj prop)
;;   (some [_ prop] (ancestors obj)))

;; (mac defprop (name (o meth?))
;;   `(do
;;      (def ,name (obj . args)
;;        ,(if meth?
;;             `(run-methods obj ',name args)
;;             `(rget obj ',name)))
;;      (defset ,name (obj) (val)
;;         `(= (,obj ',',name) ,val))))

;; (def run-methods (obj name args)
;;   (let meth (rget obj name)
;;     (if meth
;;         (apply meth obj args)
;;         (error "No method"))))