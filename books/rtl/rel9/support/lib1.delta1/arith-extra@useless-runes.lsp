(EXPT-POSITIVE-INTEGER-TYPE
 (108 108
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (43 43 (:TYPE-PRESCRIPTION NONNEG-+-TYPE))
 (11 3 (:REWRITE DEFAULT-*-2))
 (9 9 (:REWRITE POWER2-INTEGER))
 (9 9 (:REWRITE INTEGERP-MINUS))
 (7 7 (:REWRITE NON-INTEGERP-<-INTEGERP))
 (7 7
    (:REWRITE
         LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (7 7
    (:REWRITE
         LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (7 7 (:REWRITE INTEGERP-<-NON-INTEGERP))
 (7 7 (:REWRITE EXPT-COMPARE))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (7 7 (:REWRITE CANCEL-COMMON-FACTORS-IN-<))
 (7 7 (:META CANCEL_PLUS-LESSP-CORRECT))
 (7 5 (:REWRITE EXPT-WITH-I-NON-INTEGER))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (5 5 (:REWRITE EXPT-EXECUTE-REWRITE))
 (4 4 (:REWRITE EXPT-COMPARE-EQUAL))
 (4 4 (:REWRITE EQUAL-OF-PREDS-REWRITE))
 (4
   4
   (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (4 4
    (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4
    (:REWRITE CANCEL-COMMON-FACTORS-IN-EQUAL-WITH-0))
 (4 4
    (:REWRITE CANCEL-COMMON-FACTORS-IN-EQUAL))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (3 3 (:REWRITE ZIP-OPEN))
 (3 3 (:REWRITE DEFAULT-*-1)))
