; A function to subtract two bit-vectors
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Consider defining bvminus in terms of bvplus and bvuminus.

(include-book "bvchop")

(defund bvminus (size x y)
  (declare (type (integer 0 *) size))
  (bvchop size (- (ifix x) (ifix y))))

(defthm integerp-of-bvminus
  (integerp (bvminus size x y)))

(defthm natp-of-bvminus
  (natp (bvminus size x y)))

(defthm bvminus-when-arg2-is-not-an-integer
  (implies (not (integerp y))
           (equal (bvminus size x y)
                  (bvchop size x)))
  :hints (("Goal" :in-theory (enable bvminus))))

(defthm bvminus-when-size-is-not-positive
  (implies (<= size 0)
           (equal (bvminus size x y)
                  0))
  :hints (("Goal" :in-theory (enable bvminus))))

(defthm bvminus-when-size-is-not-integerp
  (implies (not (integerp size))
           (equal (bvminus size x y)
                  0))
  :hints (("Goal" :in-theory (enable bvminus))))

(defthm bvminus-same
  (equal (bvminus size x x)
         0)
  :hints (("Goal" :in-theory (enable bvminus))))

(defthm bvminus-subst-value-arg-2
  (implies (and (equal (bvchop n x) k)
                (syntaxp (and (quotep k) (not (quotep x)))))
           (equal (bvminus n x y)
                  (bvminus n k y)))
  :hints (("Goal" :in-theory (enable bvminus))))

(defthm bvminus-subst-value-arg-3
  (implies (and (equal (bvchop n x) k)
                (syntaxp (and (quotep k) (not (quotep x)))))
           (equal (bvminus n y x)
                  (bvminus n y k)))
  :hints (("Goal" :cases ((natp n))
           :in-theory (enable bvminus bvchop-of-sum-cases))))

(defthm bvminus-of-0
  (equal (bvminus size x 0)
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvminus))))

(defthm equal-of-0-and-bvminus
  (equal (equal 0 (bvminus 32 x y))
         (equal (bvchop 32 x)
                (bvchop 32 y)))
  :hints (("Goal" :in-theory (enable bvminus bvchop-of-sum-cases))))
