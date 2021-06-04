;; PL Project - Fall 2020
;; NUMEX interpreter

#lang racket
(provide (all-defined-out)) ;; so we can put tests in a second file

;; definition of structures for NUMEX programs

(struct var (string) #:transparent)  ;; a variable, e.g., (var "foo")
(struct num (int)    #:transparent)  ;; a constant number, e.g., (num 17)
(struct bool (b) #:transparent)
(struct plus (e1 e2)  #:transparent)
(struct minus (e1 e2) #:transparent)
(struct mult (e1 e2) #:transparent)
(struct div (e1 e2) #:transparent)
(struct neg (e1) #:transparent)
(struct andalso (e1 e2) #:transparent)
(struct orelse (e1 e2) #:transparent)
(struct cnd (e1 e2 e3) #:transparent)
(struct iseq (e1 e2) #:transparent)
(struct ifnzero (e1 e2 e3) #:transparent)
(struct ifleq (e1 e2 e3 e4) #:transparent)
(struct munit () #:transparent) ;; unit value -- good for ending a list
(struct ismunit (e) #:transparent) ;; if e1 is unit then true else false
(struct apair (e1 e2) #:transparent)
(struct 1st (e) #:transparent)
(struct 2nd (e) #:transparent)

(struct lam (nameopt formal body) #:transparent)
(struct apply (funexp actual) #:transparent) ;; function application
(struct with (s e1 e2) #:transparent)

;; a closure is not in "source" programs; it is what functions evaluate to
(struct closure (env f) #:transparent) 

(struct key (s e) #:transparent) ;; key holds corresponding value of s which is e
(struct record (k r) #:transparent) ;; record holds several keys
(struct value (s r) #:transparent) ;; value returns corresponding value of s in r

(struct letrec (s1 e1 s2 e2 s3 e3 s4 e4 e5) #:transparent) ;; a letrec expression for recursive definitions

;; Problem 1

(define (racketlist->numexlist xs)
  (cond [(null? xs) (munit)]
        [(list? xs) (apair (car xs) (racketlist->numexlist (cdr xs)))]
        [#t error "racketlist->numexlist: invalid input"]))

(define (numexlist->racketlist xs)
  (cond [(munit? xs) null]
        [(apair? xs) (cons (apair-e1 xs) (numexlist->racketlist (apair-e2 xs)))]
        [#t error "numexlist->racketlist: invalid input"]))

;; Problem 2

;; lookup a variable in an environment
;; Complete this function
(define (envlookup env str)
  (cond [(null? env) (error "unbound variable during evaluation" str)]
  [(list? env) (cond [(equal? str (car (car env))) (cdr (car env))]
          [#t (envlookup (cdr env) str)])]
  [#t (error "envlookup: invalid input")]))

;; Complete more cases for other kinds of NUMEX expressions.
;; We will test eval-under-env by calling it directly even though
;; "in real life" it would be a helper function of eval-exp.
(define (eval-under-env e env)
  (cond [(var? e) 
         (envlookup env (var-string e))]
        
        [(plus? e) 
         (let ([v1 (eval-under-env (plus-e1 e) env)]
               [v2 (eval-under-env (plus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (+ (num-int v1) 
                       (num-int v2)))
               (error "NUMEX addition applied to a non-number")))]
        
        [(minus? e) 
         (let ([v1 (eval-under-env (minus-e1 e) env)]
               [v2 (eval-under-env (minus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (- (num-int v1) 
                       (num-int v2)))
               (error "NUMEX substraction applied to a non-number")))]

        [(mult? e) 
         (let ([v1 (eval-under-env (mult-e1 e) env)]
               [v2 (eval-under-env (mult-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (* (num-int v1) 
                       (num-int v2)))
               (error "NUMEX multiplication applied to a non-number")))]

        [(div? e) 
         (let ([v1 (eval-under-env (div-e1 e) env)]
               [v2 (eval-under-env (div-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (if (eq? 0 (num-int v2))
                   (error "NUMEX division by zero")
               (num (quotient (num-int v1) 
                       (num-int v2))))
               (error "NUMEX division applied to a non-number")))]

        [(num? e)
          (cond [(integer? (num-int e)) e]
                [#t (error "NUMEX num applied to a non-racket-integer")])]

        [(bool? e)
          (cond [(boolean? (bool-b e)) e]
                [#t (error "NUMEX bool applied to a non-racket-boolean")])]

        [(neg? e)
         (let ([v (eval-under-env (neg-e1 e) env)])
           (cond [(num? v) (num (* -1 (num-int v)))]
                 [(bool? v)
                  (if (equal? (bool-b v) #t)
                  (bool #f)
                  (bool #t))]
                 [#t (error "NUMEX neg applied to a non-number and non-boolean")]))]
        
        [(andalso? e)
         (let ([v1 (eval-under-env (andalso-e1 e) env)])
           (if (bool? v1)
               (if (equal? (bool-b v1) #f) (bool #f)
                   (let ([v2 (eval-under-env (andalso-e2 e) env)])
                     (if (bool? v2)
                         (if (bool-b v2) (bool #t) (bool #f))
                     (error "NUMEX andalso applied to a non-boolean")))
                   )
               (error "NUMEX andalso applied to a non-boolean")))]

        [(orelse? e)
         (let ([v1 (eval-under-env (orelse-e1 e) env)])
           (if (bool? v1)
               (if (bool-b v1) (bool #t)
                   (let ([v2 (eval-under-env (orelse-e2 e) env)])
                     (if (bool? v2)
                         (if (bool-b v2) (bool #t) (bool #f))
                     (error "NUMEX orelse applied to a non-boolean")))
                   )
               (error "NUMEX orelse applied to a non-boolean")))]

        [(cnd? e)
         (let ([v1 (eval-under-env (cnd-e1 e) env)])
           (if (bool? v1)
               (if (bool-b v1) (eval-under-env (cnd-e2 e) env)
                   (eval-under-env (cnd-e3 e) env))
               (error "NUMEX cnd applied to a non-boolean")))]

        [(iseq? e)
          (let ([v1 (eval-under-env (iseq-e1 e) env)]
                [v2 (eval-under-env (iseq-e2 e) env)])
            (if (or (and (num? v1) (num? v2))
                    (and (bool? v1) (bool? v2))
                    (and (bool? v1) (num? v2))
                    (and (num? v1) (bool? v2)))
              (if (equal? v1 v2)
                (bool #t)
                (bool #f))
              (error "NUMEX iseq applied to a non-number or non-boolean or non-same-types")))]

        [(ifnzero? e)
          (let ([v (eval-under-env (ifnzero-e1 e) env)])
            (if (num? v)
              (if (equal? (num-int v) 0)
                (eval-under-env (ifnzero-e3 e) env)
                (eval-under-env (ifnzero-e2 e) env))
              (error "NUMEX isnzero applied to a non-number")))]

        [(ifleq? e)
          (let ([v1 (eval-under-env (ifleq-e1 e) env)]
                [v2 (eval-under-env (ifleq-e2 e) env)])
            (if (and (num? v1)
                     (num? v2))
              (if (> (num-int v1) 
                      (num-int v2))
                (eval-under-env (ifleq-e4 e) env)
                (eval-under-env (ifleq-e3 e) env))
              (error "NUMEX ifleq applied to a non-number")))]
        
        [(closure? e) e]

        [(apair? e)
         (apair (eval-under-env (apair-e1 e) env)
                (eval-under-env (apair-e2 e) env))]

        [(1st? e)
         (let ([v (eval-under-env (1st-e e) env)])
           (if (apair? v)
               (apair-e1 v)
               (error "NUMEX 1st applied to a non-pair")))]
        
        [(2nd? e)
         (let ([v (eval-under-env (2nd-e e) env)])
           (if (apair? v)
               (apair-e2 v)
               (error "NUMEX 2nd applied to a non-pair")))]

        [(munit? e) e]
        
        [(ismunit? e)
         (let ([v (eval-under-env (ismunit-e e) env)])
           (if (munit? v)
               (bool #t)
               (bool #f)))]

        [(lam? e)
          (if (and (or (string? (lam-nameopt e))
                       (null? (lam-nameopt e)))
                   (string? (lam-formal e)))
            (closure env e)
            (error "NUMEX lam applied to a non-string"))]

        [(apply? e)
          (let ([actual (eval-under-env (apply-actual e) env)]
                [funexp (eval-under-env (apply-funexp e) env)])
            (if (closure? funexp)
              (let ([clsrfnex (closure-f funexp)])  ;; evaluates the closure's function's body
                (if (null? (lam-nameopt clsrfnex))
                  (eval-under-env (lam-body clsrfnex) (cons (cons (lam-formal clsrfnex) actual) (closure-env funexp)))
                  (eval-under-env (lam-body clsrfnex) (cons (cons (lam-nameopt clsrfnex) funexp) (cons (cons (lam-formal clsrfnex) actual) (closure-env funexp))))))
              (if (lam? funexp)
                  (eval-under-env (apply funexp (apply-actual e)) env)
                  (error "NUMEX applied applied to a non-closure and non-lam"))))]

        [(with? e)
          (let ([v (eval-under-env (with-e1 e) env)])
            (if (string? (with-s e))
              (eval-under-env (with-e2 e) (cons (cons (with-s e) v) env))
              (error "NUMEX with applied to a non-string variable")))]
        
        [(letrec? e)
            (if (and (string? (letrec-s1 e))
                     (string? (letrec-s2 e))
                     (string? (letrec-s3 e))
                     (string? (letrec-s4 e)))
          (eval-under-env (letrec-e5 e)
                          (cons (cons (letrec-s1 e)
                                      (letrec-e1 e))
                                (cons (cons (letrec-s2 e)
                                            (letrec-e2 e))
                                      (cons (cons (letrec-s3 e)
                                                  (letrec-e3 e))
                                          (cons (cons (letrec-s4 e)
                                                      (letrec-e4 e)) env)))))
              (error "NUMEX letrec inputs are invalid"))]
       
        [(key? e)
          (let ([v (eval-under-env (key-e e) env)])
            (if (string? (key-s e))
              (key (key-s e) v)
              (error "NUMEX key applied to a non-string key")))]
        
        [(record? e)
          (let ([v1 (eval-under-env (record-k e) env)]
                [v2 (eval-under-env (record-r e) env)])
            (if (and (key? v1)
                     (munit? v2))
              (record v1 v2)
              (if (and (key? v1)
                       (record? v2))
                (record v1 v2)
                (error "NUMEX record inputs are invalid"))))]

        [(value? e)
          (let ([v (eval-under-env (value-r e) env)])
            (if (and (string? (value-s e))
                     (record? v))
              (if (munit? (record-r v))
                  (if (equal? (key-s (record-k v))
                              (value-s e))
                    (key-e (record-k v))
                    (munit))  ;; if there is no s as a key in record r
                  (if (equal? (key-s (record-k v))
                              (value-s e))
                        (key-e (record-k v))
                        (eval-under-env (value (value-s e) (record-r v)) env)))
              (error "NUMEX value inputs are invalid")))]
        
        [else (error (format "bad NUMEX expression: ~v" e))]))

;; Do NOT change
(define (eval-exp e)
  (eval-under-env e null))
        
;; Problem 3

(define (ifmunit e1 e2 e3)
  (cnd (ismunit  e1) e2 e3))

(define (with* bs e2)
  (if (null? bs) e2
      (with (car (car bs)) (cdr (car bs)) (with* (cdr bs) e2))))

(define (ifneq e1 e2 e3 e4)
  (cnd (iseq e1 e2) e4 e3))

;; Problem 4

(define numex-filter
  (lam null "fltrFunc"
    (lam "mapFunc" "lst"
      (cnd (ismunit (var "lst"))
        (munit)
        (ifnzero (apply (var "fltrFunc") (1st (var "lst"))) ;; returns a number other than zero
          (apair (apply (var "fltrFunc") (1st (var "lst")))
                 (apply (var "mapFunc") (2nd (var "lst"))))
          (apply (var "mapFunc") (2nd (var "lst")))))))) ;; if ifnzero is false

(define numex-all-gt
  (with "filter" numex-filter
    (lam null "i"
      (lam null "lst"
         (apply (apply (var "filter")
                     (lam "gt" "num" ;; filters numbers lower than i
                         (ifleq (var "num") (var "i")
                                (num 0) ;; nothing happens when we pass 0 to numex-filter.
                                (var "num"))))
                   (var "lst")))))) ;; applying to lst

;; Challenge Problem

(struct fun-challenge (nameopt formal body freevars) #:transparent) ;; a recursive(?) 1-argument function

;; We will test this function directly, so it must do
;; as described in the assignment
(define (compute-free-vars e) "CHANGE")

;; Do NOT share code with eval-under-env because that will make grading
;; more difficult, so copy most of your interpreter here and make minor changes
(define (eval-under-env-c e env) "CHANGE")

;; Do NOT change this
(define (eval-exp-c e)
  (eval-under-env-c (compute-free-vars e) null))
