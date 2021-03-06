(APPEND-ONE-AND-K-ZEROS-AND-LEN
 (6
   6
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (6
  6
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(APPEND-MESSAGE-0BYTES
     (210 11
          (:REWRITE NUM-CHARS-EQUALS-NUM-BYTES))
     (132 14 (:DEFINITION CHARACTER-LISTP))
     (124 8 (:REWRITE CHARACTER-LISTP-APPEND))
     (68 36 (:REWRITE DEFAULT-CDR))
     (64 56
         (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (61 61 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
     (56 56 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (45 7 (:DEFINITION BINARY-APPEND))
     (39 23 (:REWRITE DEFAULT-CAR))
     (21 11 (:REWRITE DEFAULT-PLUS-2))
     (20 20 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (20 4 (:DEFINITION TRUE-LISTP))
     (16 8
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (16 8
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (11 11
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (11 11 (:REWRITE NORMALIZE-ADDENDS))
     (11 11 (:REWRITE DEFAULT-PLUS-1))
     (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 8
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (8 8
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (8 8
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (8 8 (:REWRITE |(equal c (/ x))|))
     (8 8 (:REWRITE |(equal c (- x))|))
     (8 8 (:REWRITE |(equal (/ x) c)|))
     (8 8 (:REWRITE |(equal (/ x) (/ y))|))
     (8 8 (:REWRITE |(equal (- x) c)|))
     (8 8 (:REWRITE |(equal (- x) (- y))|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(NEW-TEMP-LEMMA (786 42
                     (:REWRITE NUM-CHARS-EQUALS-NUM-BYTES))
                (460 45 (:DEFINITION CHARACTER-LISTP))
                (327 150
                     (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                (248 13 (:REWRITE CHARACTER-LISTP-APPEND))
                (215 215 (:TYPE-PRESCRIPTION TRUE-LISTP))
                (205 205
                     (:TYPE-PRESCRIPTION CHARACTER-LISTP))
                (155 13 (:DEFINITION TRUE-LISTP))
                (153 72 (:REWRITE DEFAULT-PLUS-2))
                (150 150 (:TYPE-PRESCRIPTION BINARY-APPEND))
                (132 111 (:REWRITE DEFAULT-CDR))
                (98 72 (:REWRITE DEFAULT-PLUS-1))
                (77 65 (:REWRITE DEFAULT-CAR))
                (62 62
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (62 62 (:REWRITE NORMALIZE-ADDENDS))
                (40 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (40 9
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (40 9
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (9 9
                   (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                (9 9
                   (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                (9 9
                   (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                (9 9 (:REWRITE |(equal c (/ x))|))
                (9 9 (:REWRITE |(equal c (- x))|))
                (9 9 (:REWRITE |(equal (/ x) c)|))
                (9 9 (:REWRITE |(equal (/ x) (/ y))|))
                (9 9 (:REWRITE |(equal (- x) c)|))
                (9 9 (:REWRITE |(equal (- x) (- y))|))
                (9 9 (:REWRITE |(equal (+ (- c) x) y)|))
                (5 5 (:REWRITE FOLD-CONSTS-IN-+))
                (5 5 (:REWRITE |(+ c (+ d x))|)))
(HELP-LEMMA-FOR-APPEND-55)
(APPEND-MESSAGE-55BYTES
     (18 2 (:REWRITE NUM-CHARS-EQUALS-NUM-BYTES))
     (12 2 (:DEFINITION CHARACTER-LISTP))
     (12 2 (:DEFINITION BINARY-APPEND))
     (10 10 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
     (8 6 (:REWRITE DEFAULT-CDR))
     (6 4 (:REWRITE DEFAULT-CAR))
     (4 2 (:REWRITE DEFAULT-PLUS-2))
     (3 3
        (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (3 3 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE DEFAULT-PLUS-1))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|)))
(HELP-LEMMA-FOR-APPEND-56)
(APPEND-MESSAGE-56BYTES
     (18 2 (:REWRITE NUM-CHARS-EQUALS-NUM-BYTES))
     (12 2 (:DEFINITION CHARACTER-LISTP))
     (12 2 (:DEFINITION BINARY-APPEND))
     (10 10 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
     (8 6 (:REWRITE DEFAULT-CDR))
     (6 4 (:REWRITE DEFAULT-CAR))
     (4 2 (:REWRITE DEFAULT-PLUS-2))
     (3 3
        (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (3 3 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE DEFAULT-PLUS-1))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|)))
(HELP-LEMMA-FOR-APPEND-119)
(APPEND-MESSAGE-119BYTES
     (18 2 (:REWRITE NUM-CHARS-EQUALS-NUM-BYTES))
     (12 2 (:DEFINITION CHARACTER-LISTP))
     (12 2 (:DEFINITION BINARY-APPEND))
     (10 10 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
     (8 6 (:REWRITE DEFAULT-CDR))
     (6 4 (:REWRITE DEFAULT-CAR))
     (4 2 (:REWRITE DEFAULT-PLUS-2))
     (3 3
        (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (3 3 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE DEFAULT-PLUS-1))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|)))
(SHA-EXPAND-LOOP
     (60 60 (:REWRITE DEFAULT-PLUS-2))
     (36 4 (:REWRITE ACL2-NUMBERP-X))
     (23 23 (:REWRITE THE-FLOOR-BELOW))
     (23 23 (:REWRITE THE-FLOOR-ABOVE))
     (23 23 (:REWRITE DEFAULT-LESS-THAN-2))
     (23 23 (:REWRITE DEFAULT-LESS-THAN-1))
     (19 19
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (19 19
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (19 19
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (19 19
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (19 19
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (19 19
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (19 19
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (19 19 (:REWRITE |(< c (- x))|))
     (19 19
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (19 19
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (19 19
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (19 19
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (19 19 (:REWRITE |(< (/ x) (/ y))|))
     (19 19 (:REWRITE |(< (- x) (- y))|))
     (17 17
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (17 17 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (17 17
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (17 17 (:REWRITE INTEGERP-<-CONSTANT))
     (17 17 (:REWRITE CONSTANT-<-INTEGERP))
     (16 4 (:REWRITE RATIONALP-X))
     (9 9 (:REWRITE REDUCE-INTEGERP-+))
     (9 9
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (9 9 (:REWRITE INTEGERP-MINUS-X))
     (9 9 (:REWRITE |(< (/ x) 0)|))
     (9 9 (:REWRITE |(< (* x y) 0)|))
     (9 9 (:META META-INTEGERP-CORRECT))
     (8 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5 (:REWRITE |(< (+ c/d x) y)|))
     (5 5 (:REWRITE |(< (+ (- c) x) y)|))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:META META-RATIONALP-CORRECT))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (3 3 (:REWRITE |(+ c (+ d x))|))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|)))
(SHA-MAIN-LOOP1)
(SHA-MAIN-LOOP)
(SHA-LOOP)
(SHA-ENCRYPT1)
(SHA-ENCRYPT)
(SHA-2)
(SHA-256-TEST-CASE-1)
(SHA-256-TEST-CASE-2)
(SHA-256-TEST-CASE-3)
