;;; Contributed by Keshav Kini

; This is a very basic library for reasoning about complex arithmetic.

; License: A 3-clause BSD license.  See the LICENSE file distributed
; with ACL2.

(in-package "ACL2")

(local (include-book "equalities"))

(defthm realpart-complex-to-realfix
  (equal (realpart (complex x y))
         (realfix x))
  :hints (("Goal" :use completion-of-complex)))

(defthm imagpart-complex-to-realfix
  (equal (imagpart (complex x y))
         (realfix y))
  :hints (("Goal" :use completion-of-complex)))

(in-theory (disable realpart-complex imagpart-complex))

; ================================================================

(defthm conjugate-involutive
  (equal (conjugate (conjugate x)) (fix x)))

; ================================================================

(local (in-theory (enable complex-definition)))

(defthm add-def-complex ; from axioms.lisp
  (equal (+ x y)
         (complex (+ (realpart x) (realpart y))
                  (+ (imagpart x) (imagpart y))))
  :rule-classes nil)

(defthm unary--def-complex
  (equal (- x)
         (complex (- (realpart x))
                  (- (imagpart x))))
  :rule-classes nil)

(defthm mul-def-complex
  (equal (* x y)
         (complex (- (* (realpart x) (realpart y))
                     (* (imagpart x) (imagpart y)))
                  (+ (* (realpart x) (imagpart y))
                     (* (imagpart x) (realpart y)))))
  :rule-classes nil)

(defthm complex-norm-squared
  ;; so named because $|z| = \sqrt{z\overline z}$
  (equal (* x (conjugate x))
         (+ (* (realpart x) (realpart x))
            (* (imagpart x) (imagpart x)))))

(local
 (defthmd distribute-*-over-implicit-+-in-complex
   (implies (and (real/rationalp a)
                 (real/rationalp b)
                 (real/rationalp c))
            (equal (* (complex a b) c)
                   (complex (* a c) (* b c))))))

(local (in-theory (disable complex-definition)))

(skip-proofs
 (local
  (defthm conjugate-of-nonzero-is-nonzero
    (implies (and (acl2-numberp x)
                  (not (equal x 0)))
             (not (equal (conjugate x) 0))))))

(local
 (defthm crock
   (equal (/ x)
          (if (and (acl2-numberp x)
                   (not (zerop x)))
              (/ (conjugate x)
                 (* x (conjugate x)))
            0))
   :hints (("Goal" :in-theory (disable conjugate)))
   :rule-classes nil))

(defthm div-def-complex-1
  (equal (/ x)
         (/ (conjugate x)
            (+ (* (realpart x) (realpart x))
               (* (imagpart x) (imagpart x)))))
  :hints (("Goal" :use (crock
                        complex-norm-squared
                        )))
  :rule-classes nil)

(defthm div-def-complex-2
  (equal (/ x)
         (complex (/ (realpart x)
                     (+ (* (realpart x) (realpart x))
                        (* (imagpart x) (imagpart x))))
                  (/ (- (imagpart x))
                     (+ (* (realpart x) (realpart x))
                        (* (imagpart x) (imagpart x))))))
  :hints (("Goal"
           :use div-def-complex-1
           :in-theory (enable distribute-*-over-implicit-+-in-complex)))
  :rule-classes nil)

; ================================================================

(defthm conjugate*
  (equal (conjugate x)
         (if (acl2-numberp x)
             (complex (realpart x) (- (imagpart x)))
           x))
  :rule-classes :definition)

(in-theory (disable conjugate))

(defthm conjugate-when-maybe-complex
  (or (complex/complex-rationalp (conjugate x))
      (equal (conjugate x) x))
  :rule-classes :type-prescription)

(defthm conjugate-when-not-complex-rational
  (implies (not (complex-rationalp x))
           #-:non-standard-analysis
           (equal (conjugate x) x)
           #+:non-standard-analysis
           (or (and (complexp (conjugate x))
                    (not (complex-rationalp (conjugate x))))
               (equal (conjugate x) x)))
  :rule-classes :type-prescription)

#+:non-standard-analysis
(defthm conjugate-when-maybe-complex-rational
  (implies (or (not (complex/complex-rationalp x))
               (complex-rationalp x))
           (or (complex-rationalp (conjugate x))
               (equal (conjugate x) x)))
  :rule-classes :type-prescription)

; ================================================================

(in-theory (disable complex-equal))

(defthm equal-complex
  (equal (equal (complex x y) z)
         (and (acl2-numberp z)
              (equal (realfix x) (realpart z))
              (equal (realfix y) (imagpart z)))))

(defthm realpart-conjugate
  (equal (realpart (conjugate x))
         (realpart x)))

(defthm imagpart-conjugate
  (equal (imagpart (conjugate x))
         (- (imagpart x))))

(defthm realpart-+ ; from axioms.lisp
  (equal (realpart (+ x y))
         (+ (realpart x) (realpart y)))
  :hints (("Goal" :use add-def-complex)))

(defthm imagpart-+ ; from axioms.lisp
  (equal (imagpart (+ x y))
         (+ (imagpart x) (imagpart y)))
  :hints (("Goal" :use add-def-complex)))

(defthm conjugate-+
  (equal (conjugate (+ x y))
         (+ (conjugate x) (conjugate y))))

(defthm realpart--
  (equal (realpart (- x))
         (- (realpart x)))
  :hints (("Goal" :in-theory (disable realpart-+)
           :use ((:instance realpart-+ (y (- x)))))))

(defthm imagpart--
  (equal (imagpart (- x))
         (- (imagpart x)))
  :hints (("Goal" :in-theory (disable imagpart-+)
           :use ((:instance imagpart-+ (y (- x)))))))

(defthm conjugate--
  (equal (conjugate (- x))
         (- (conjugate x))))

(defthm realpart-*
  (equal (realpart (* x y))
         (- (* (realpart x) (realpart y))
            (* (imagpart x) (imagpart y))))
  :hints (("Goal" :use mul-def-complex)))

(defthm imagpart-*
  (equal (imagpart (* x y))
         (+ (* (realpart x) (imagpart y))
            (* (imagpart x) (realpart y))))
  :hints (("Goal" :use mul-def-complex)))

(defthm conjugate-*
  (equal (conjugate (* x y))
         (* (conjugate x) (conjugate y))))

(defthm realpart-/
  (equal (realpart (/ x))
         (/ (realpart x)
            (+ (* (realpart x) (realpart x))
               (* (imagpart x) (imagpart x)))))
  :hints (("Goal" :use div-def-complex-2)))

(defthm imagpart-/
  (equal (imagpart (/ x))
         (/ (- (imagpart x))
            (+ (* (realpart x) (realpart x))
               (* (imagpart x) (imagpart x)))))
  :hints (("Goal" :use div-def-complex-2)))

(defthm conjugate-/
  (equal (conjugate (/ x))
         (/ (conjugate x))))

(in-theory (disable conjugate*))
