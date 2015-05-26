#lang racket

;; λSR is the language of subrange numbers. Each number can exist as an n-dimensional range
;; and all arithmetic operations are distributed accordingly (promoting lower dimensional 
;; numbers to higher ones, etc.) λSR implements standard arithmetic, simplified conditionals,
;; numeric values, variables, and simple errors. It does not currently include a type system.
;; For the moment, all elements in the language are numberic.

;; Author: Garrett Bluma
;; Date: May 24, 2015
;; License: LGPL
 
(require redex)

(define-language λSR
  (e x v (if0 e e e) (branch e e) (arith e e) (err string))  ; expressions
  (arith + - * /) ; arithmetic
  (v number unknown (λ (x ...) e) (range e e)) ; values
  (x (variable-except λ + - * / arith number unknown branch range err if0))
  
  ; PLT Redex debugging
  (E (v ... E e ...) (if0 E e e) (if0 e E e) (if0 e e E) 
     (arith e E) (arith E e) (branch E e) (branch e E) (err E) 
     hole)
  )


(define λSR-redex
  (reduction-relation
   λSR
;   this will be handled in parsing
;   (--> (in-hole E number_1)
;        (in-hole E (range number_1 number_1))
;        "R-intro")
   
;   handled in printing
;   (--> (in-hole E (range number_1 number_1))
;        (in-hole E number_1)
;        "R-elim1")
   
   (--> (in-hole E (branch v_1 v_1))
        (in-hole E v_1)
        "B-elim1")
   
   (--> (in-hole E (+ (range number_1 number_2)
                      (range number_3 number_4)))
        (in-hole E (range ,(+ (term number_1) (term number_3))
                          ,(+ (term number_2) (term number_4))))
        "+_RR")
   
   (--> (in-hole E (- (range number_1 number_2)
                      (range number_3 number_4)))
        (in-hole E (range ,(- (term number_1) (term number_3))
                          ,(- (term number_2) (term number_4))))
        "-_RR")
   
   (--> (in-hole E (* (range number_1 number_2)
                      (range number_3 number_4)))
        (in-hole E (range ,(* (term number_1) (term number_3))
                          ,(* (term number_2) (term number_4))))
        "*_RR")
   
   (--> (in-hole E (/ (range number_1 number_2)
                      (range number_3 number_4)))
        (in-hole E (range ,(/ (term number_1) (term number_3))
                          ,(/ (term number_2) (term number_4))))
        "/_RR"
        (side-condition (and (not (= 0 (term number_3))) 
                             (not (= 0 (term number_4))))))
   
   (--> (in-hole E (/ (range number_1 number_2)
                      (range 0 number_4)))
        (in-hole E (err "Division by zero"))
        "/_RR0a"
        )
   
   (--> (in-hole E (/ (range number_1 number_2)
                      (range number_3 0)))
        (in-hole E (err "Division by zero"))
        "/_RR0b"
        )
   
   (--> (in-hole E (arith (branch e_1 e_2) (branch e_3 e_4)))
        (in-hole E (branch 
                    (branch (arith e_1 e_3) (a e_1 e_4))
                    (branch (arith e_2 e_3) (a e_2 e_4))))
        "arith_BB")
   
   (--> (in-hole E (arith e_1 (branch e_2 e_3)))
        (in-hole E (branch (arith e_1 e_2)
                           (arith e_1 e_3)))
        "arith_eB")
   
   (--> (in-hole E (arith (branch e_1 e_2) e_3))
        (in-hole E (branch (arith e_1 e_3)
                           (arith e_2 e_3)))
        "arith_Be")
   
   (--> (in-hole E (if0 (range 0 0) e_1 e_2))
        (in-hole E e_1)
        "if0t")
   
   (--> (in-hole E (if0 (range number_1 number_2) e_2 e_3))
        (in-hole E e_3)
        "if0f"
        (side-condition (and (not (= 0 (term number_1))) 
                             (not (= 0 (term number_2))))))
   
   (--> (in-hole E (if0 unknown e_2 e_3))
        (in-hole E (branch e_2 e_3))
        "if0_x")
   
   (--> (in-hole E ((λ (x ..._1) e) v ..._1))
        (in-hole E (subst-n (x v) ... e))
        "βv")
   ))

(define-metafunction λSR
  subst-n : (x any) ... any -> any
  [(subst-n (x_1 any_1) (x_2 any_2) ... any_3)
   (subst x_1 any_1 (subst-n (x_2 any_2) ... 
                             any_3))]
  [(subst-n any_3) any_3])

(define-metafunction λSR
  subst : x any any -> any
  ;; 1. x_1 bound, so don't continue in λ body
  [(subst x_1 any_1 (λ (x_2 ... x_1 x_3 ...) any_2))
   (λ (x_2 ... x_1 x_3 ...) any_2)
   (side-condition (not (member (term x_1)
                                (term (x_2 ...)))))]
  ;; 2. general purpose capture avoiding case
  [(subst x_1 any_1 (λ (x_2 ...) any_2))
   (λ (x_new ...) 
     (subst x_1 any_1
            (subst-vars (x_2 x_new) ... 
                        any_2)))
   (where (x_new ...)
          ,(variables-not-in
            (term (x_1 any_1 any_2)) 
            (term (x_2 ...))))]
  ;; 3. replace x_1 with e_1
  [(subst x_1 any_1 x_1) any_1]
  ;; 4. x_1 and x_2 are different, so don't replace
  [(subst x_1 any_1 x_2) x_2]
  ;; the last cases cover all other expressions
  [(subst x_1 any_1 (any_2 ...))
   ((subst x_1 any_1 any_2) ...)]
  [(subst x_1 any_1 any_2) any_2])

(define-metafunction λSR
  subst-vars : (x any) ... any -> any
  [(subst-vars (x_1 any_1) x_1) any_1]
  [(subst-vars (x_1 any_1) (any_2 ...)) 
   ((subst-vars (x_1 any_1) any_2) ...)]
  [(subst-vars (x_1 any_1) any_2) any_2]
  [(subst-vars (x_1 any_1) (x_2 any_2) ... any_3) 
   (subst-vars (x_1 any_1) 
               (subst-vars (x_2 any_2) ... any_3))]
  [(subst-vars any) any])





(test-->> λSR-redex (term ((λ (n) n) (range 0 0)) ) (term (range 0 0) ))
(test-->> λSR-redex (term ((λ (n) n) (range 100 100)) ) (term (range 100 100) ))

; interesting example 1
;(traces λSR-redex (term ((λ (n) (+ n (range 1 1))) (range 1 1)) ))
(test-->> λSR-redex (term ((λ (n) (+ n (range 1 1))) (range 1 1))) (term (range 2 2) ))
(test-->> λSR-redex (term ((λ (n) (* n (range 2 2))) (range 2 2))) (term (range 4 4) ))
(test-->> λSR-redex (term ((λ (n) (- n (range 2 2))) (range 2 2))) (term (range 0 0) ))
(test-->> λSR-redex (term ((λ (n) (/ n (range 2 2))) (range 8 8))) (term (range 4 4) ))

(test-->> λSR-redex 
          (term ((λ (n) (+ n (range 1 2))) (range 2 2))) 
          (term (range 3 4) ))

(test-->> λSR-redex 
          (term ((λ (n) (+ n (range 1 2))) (range 10 11))) 
          (term (range 11 13) ))

(test-->> λSR-redex 
          (term ((λ (n) (+ n (if0 unknown (range 1 1) (range 2 2)))) (range 2 2))) 
          (term (branch (range 3 3) (range 4 4)) ))

(test-->> λSR-redex 
          (term (/ (range 1 1) (if0 unknown (range 0 5) (range 4 5)))) 
          (term (branch (err "Division by zero") (range 1/4 1/5))))

(test-->> λSR-redex
          (term ((λ (n) (/ (range 1 1) (if0 unknown (range 4 5) n))) (- (range 2 2) (range 2 2))))
          (term (branch (range 1/4 1/5) (err "Division by zero"))))

; interesting example 2
;(traces λSR-redex
;          (term ((λ (n) (/ (range 1 1) (if0 unknown (range 4 5) n))) (- (range 2 2) (range 2 2)))))


(traces λSR-redex
          (term (range (range 1 2) (range 1 4))))
