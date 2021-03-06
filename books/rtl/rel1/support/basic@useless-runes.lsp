(CG)
(FL-MONOTONE)
(CG-MONOTONE (10 10 (:REWRITE A10))
             (5 4 (:REWRITE DEFAULT-+-2))
             (5 4 (:REWRITE DEFAULT-+-1))
             (4 4 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
             (3 2 (:REWRITE DEFAULT-<-2))
             (3 2 (:REWRITE DEFAULT-<-1))
             (2 2 (:REWRITE DEFAULT-*-2))
             (2 2 (:REWRITE DEFAULT-*-1)))
(INT-FL)
(INT-CG)
(FL-INT (12 4 (:LINEAR A13))
        (4 4 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
        (4 4 (:LINEAR FL-WEAKLY-MONOTONIC . 1))
        (2 2 (:REWRITE DEFAULT-+-2))
        (2 2 (:REWRITE DEFAULT-+-1)))
(FL-INT-2 (12 4 (:LINEAR A13))
          (4 4 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
          (4 4 (:LINEAR FL-WEAKLY-MONOTONIC . 1))
          (2 2 (:REWRITE DEFAULT-+-2))
          (2 2 (:REWRITE DEFAULT-+-1))
          (1 1 (:REWRITE A10)))
(CG-INT (12 4 (:LINEAR A13))
        (4 4 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
        (4 4 (:LINEAR FL-WEAKLY-MONOTONIC . 1))
        (2 2 (:REWRITE DEFAULT-+-2))
        (2 2 (:REWRITE DEFAULT-+-1))
        (2 2 (:REWRITE DEFAULT-*-2))
        (2 2 (:REWRITE DEFAULT-*-1)))
(CG-INT-2 (12 4 (:LINEAR A13))
          (6 4 (:REWRITE DEFAULT-*-2))
          (5 4 (:REWRITE DEFAULT-+-2))
          (5 4 (:REWRITE DEFAULT-+-1))
          (4 4 (:REWRITE DEFAULT-*-1))
          (4 4 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
          (4 4 (:LINEAR FL-WEAKLY-MONOTONIC . 1))
          (1 1 (:REWRITE A10)))
(FL-DEF (11 4 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
        (5 5 (:REWRITE A10))
        (4 2 (:REWRITE DEFAULT-<-2))
        (2 2 (:REWRITE DEFAULT-<-1))
        (2 1 (:REWRITE DEFAULT-+-2))
        (1 1 (:REWRITE DEFAULT-+-1)))
(CG-DEF (9 7 (:REWRITE DEFAULT-+-2))
        (9 7 (:REWRITE DEFAULT-+-1))
        (5 5 (:REWRITE FL-INT))
        (5 5 (:REWRITE A10))
        (4 4 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
        (4 4 (:LINEAR FL-WEAKLY-MONOTONIC . 1))
        (3 2 (:REWRITE DEFAULT-<-2))
        (2 2 (:REWRITE DEFAULT-<-1))
        (2 2 (:REWRITE DEFAULT-*-2))
        (2 2 (:REWRITE DEFAULT-*-1))
        (2 2 (:REWRITE A4))
        (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(FL-UNIQUE (6 6 (:REWRITE A10))
           (5 1 (:REWRITE A4))
           (3 3 (:REWRITE DEFAULT-+-2))
           (3 3 (:REWRITE DEFAULT-+-1))
           (2 1 (:REWRITE UNICITY-OF-0))
           (1 1 (:DEFINITION FIX)))
(CG-UNIQUE (8 8 (:REWRITE A10))
           (3 3 (:REWRITE DEFAULT-+-2))
           (3 3 (:REWRITE DEFAULT-+-1)))
(N<=FL (1 1 (:REWRITE A10)))
(N>=CG (1 1 (:REWRITE A10)))
(FL+INT (19 13 (:REWRITE DEFAULT-+-2))
        (15 15 (:REWRITE FL-INT))
        (14 13 (:REWRITE DEFAULT-+-1))
        (8 8 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
        (8 8 (:LINEAR FL-WEAKLY-MONOTONIC . 1))
        (2 2 (:REWRITE FOLD-CONSTS-IN-+))
        (2 2 (:REWRITE A4)))
(CG+INT (8 8 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
        (8 8 (:LINEAR FL-WEAKLY-MONOTONIC . 1))
        (7 7 (:REWRITE FL-INT))
        (7 7 (:REWRITE A10))
        (3 3 (:REWRITE DEFAULT-+-2))
        (3 3 (:REWRITE DEFAULT-+-1)))
(FL/INT-1 (18 9 (:REWRITE FL-INT))
          (18 9 (:REWRITE A10))
          (7 4 (:REWRITE DEFAULT-<-2))
          (5 4 (:REWRITE DEFAULT-<-1))
          (5 4 (:REWRITE DEFAULT-*-2))
          (5 4 (:REWRITE DEFAULT-*-1))
          (5 3 (:REWRITE DEFAULT-+-2))
          (4 4 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
          (4 4 (:LINEAR FL-WEAKLY-MONOTONIC . 1))
          (3 3 (:REWRITE DEFAULT-+-1))
          (2 2 (:REWRITE DEFAULT-UNARY-/))
          (2 2
             (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 2))
          (2 2
             (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 1))
          (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 2))
          (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 1))
          (2 2
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 2))
          (2 2
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 1))
          (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 2))
          (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 1)))
(FL/INT-2 (108 83 (:REWRITE DEFAULT-*-2))
          (95 83 (:REWRITE DEFAULT-*-1))
          (59 38 (:REWRITE FL-INT))
          (59 38 (:REWRITE A10))
          (34 18 (:REWRITE DEFAULT-<-2))
          (33 33 (:REWRITE DEFAULT-UNARY-/))
          (32 8
              (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 2))
          (31 8 (:LINEAR *-STRONGLY-MONOTONIC . 2))
          (27 18 (:REWRITE DEFAULT-<-1))
          (13 7 (:REWRITE DEFAULT-+-2))
          (10 8
              (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 1))
          (8 8
             (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 2))
          (8 8
             (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 1))
          (8 8 (:LINEAR *-WEAKLY-MONOTONIC . 2))
          (8 8 (:LINEAR *-WEAKLY-MONOTONIC . 1))
          (7 7 (:REWRITE DEFAULT-+-1))
          (4 4 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
          (4 4 (:LINEAR FL-WEAKLY-MONOTONIC . 1)))
(FL/INT (48 21 (:REWRITE FL-INT))
        (48 21 (:REWRITE A10))
        (15 12 (:REWRITE DEFAULT-*-2))
        (15 12 (:REWRITE DEFAULT-*-1))
        (12 12 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
        (12 12 (:LINEAR FL-WEAKLY-MONOTONIC . 1))
        (9 6 (:REWRITE DEFAULT-+-2))
        (7 5 (:REWRITE DEFAULT-<-2))
        (7 5 (:REWRITE DEFAULT-<-1))
        (6 6 (:REWRITE DEFAULT-UNARY-/))
        (6 6 (:REWRITE DEFAULT-+-1))
        (6 6
           (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 2))
        (6 6
           (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 1))
        (6 6 (:LINEAR *-WEAKLY-MONOTONIC . 2))
        (6 6 (:LINEAR *-WEAKLY-MONOTONIC . 1))
        (6 6
           (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 2))
        (6 6
           (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 1))
        (6 6 (:LINEAR *-STRONGLY-MONOTONIC . 2))
        (6 6 (:LINEAR *-STRONGLY-MONOTONIC . 1)))
(FL-CG (8 8 (:REWRITE FL-INT))
       (8 8 (:REWRITE A10))
       (8 8 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
       (8 8 (:LINEAR FL-WEAKLY-MONOTONIC . 1))
       (4 4 (:REWRITE DEFAULT-+-2))
       (4 4 (:REWRITE DEFAULT-+-1)))
(CG/INT-1 (39 30 (:REWRITE DEFAULT-*-2))
          (34 30 (:REWRITE DEFAULT-*-1))
          (19 13 (:REWRITE DEFAULT-+-2))
          (18 13 (:REWRITE DEFAULT-+-1))
          (16 10 (:REWRITE FL-INT))
          (16 10 (:REWRITE A10))
          (9 6 (:REWRITE DEFAULT-<-2))
          (8 8 (:REWRITE DEFAULT-UNARY-/))
          (8 6 (:REWRITE DEFAULT-<-1))
          (2 2 (:REWRITE A4))
          (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(CG/INT-2 (144 109 (:REWRITE DEFAULT-*-2))
          (116 109 (:REWRITE DEFAULT-*-1))
          (46 29 (:REWRITE DEFAULT-+-2))
          (42 29 (:REWRITE DEFAULT-+-1))
          (34 25 (:REWRITE FL-INT))
          (34 25 (:REWRITE A10))
          (28 28 (:REWRITE DEFAULT-UNARY-/))
          (21 12 (:REWRITE DEFAULT-<-2))
          (18 12 (:REWRITE DEFAULT-<-1))
          (2 2 (:REWRITE A4))
          (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(CG/INT (48 21 (:REWRITE FL-INT))
        (48 21 (:REWRITE A10))
        (41 28 (:REWRITE DEFAULT-*-2))
        (31 28 (:REWRITE DEFAULT-*-1))
        (20 13 (:REWRITE DEFAULT-+-2))
        (17 13 (:REWRITE DEFAULT-+-1))
        (12 12 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
        (12 12 (:LINEAR FL-WEAKLY-MONOTONIC . 1))
        (7 5 (:REWRITE DEFAULT-<-2))
        (7 5 (:REWRITE DEFAULT-<-1))
        (6 6 (:REWRITE DEFAULT-UNARY-/))
        (6 6
           (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 2))
        (6 6
           (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 1))
        (6 6 (:LINEAR *-WEAKLY-MONOTONIC . 2))
        (6 6 (:LINEAR *-WEAKLY-MONOTONIC . 1))
        (6 6
           (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 2))
        (6 6
           (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 1))
        (6 6 (:LINEAR *-STRONGLY-MONOTONIC . 2))
        (6 6 (:LINEAR *-STRONGLY-MONOTONIC . 1)))
(DELTA1-1 (46 46 (:REWRITE DEFAULT-*-2))
          (46 46 (:REWRITE DEFAULT-*-1))
          (26 12
              (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 1))
          (12 12
              (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 2))
          (12 12
              (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 2))
          (12 12
              (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 1))
          (12 12 (:LINEAR *-STRONGLY-MONOTONIC . 2))
          (12 12 (:LINEAR *-STRONGLY-MONOTONIC . 1))
          (8 8 (:REWRITE DEFAULT-<-2))
          (8 8 (:REWRITE DEFAULT-<-1))
          (8 8 (:REWRITE DEFAULT-+-2))
          (8 8 (:REWRITE DEFAULT-+-1))
          (8 8 (:REWRITE A5))
          (5 1 (:REWRITE COMMUTATIVITY-OF-+))
          (2 1 (:REWRITE UNICITY-OF-0)))
(DELTA1-A (51 51 (:REWRITE DEFAULT-*-2))
          (51 51 (:REWRITE DEFAULT-*-1))
          (26 25 (:REWRITE DEFAULT-+-2))
          (25 25 (:REWRITE DEFAULT-+-1))
          (19 19 (:REWRITE A4))
          (14 14
              (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 2))
          (14 14
              (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 1))
          (14 14
              (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 2))
          (14 14
              (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 1))
          (14 14 (:LINEAR *-STRONGLY-MONOTONIC . 2))
          (14 14 (:LINEAR *-STRONGLY-MONOTONIC . 1))
          (8 8 (:REWRITE FOLD-CONSTS-IN-+))
          (8 8 (:REWRITE DEFAULT-<-2))
          (8 8 (:REWRITE DEFAULT-<-1)))
(DELTA1-B (45 45 (:REWRITE DEFAULT-*-2))
          (45 45 (:REWRITE DEFAULT-*-1))
          (24 24 (:REWRITE DEFAULT-+-2))
          (24 24 (:REWRITE DEFAULT-+-1))
          (17 17 (:REWRITE A4))
          (10 10
              (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 2))
          (10 10
              (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 1))
          (10 10
              (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 2))
          (10 10
              (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 1))
          (10 10 (:LINEAR *-STRONGLY-MONOTONIC . 2))
          (10 10 (:LINEAR *-STRONGLY-MONOTONIC . 1))
          (8 8 (:REWRITE DEFAULT-<-2))
          (8 8 (:REWRITE DEFAULT-<-1))
          (7 7 (:REWRITE FOLD-CONSTS-IN-+)))
(DELTA2 (21 21 (:REWRITE DEFAULT-+-2))
        (21 21 (:REWRITE DEFAULT-+-1))
        (21 21 (:REWRITE DEFAULT-*-2))
        (21 21 (:REWRITE DEFAULT-*-1))
        (12 12 (:REWRITE A4))
        (7 7 (:REWRITE FOLD-CONSTS-IN-+))
        (5 5 (:REWRITE A5))
        (4 4
           (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 2))
        (4 4
           (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 1))
        (4 4 (:LINEAR *-WEAKLY-MONOTONIC . 2))
        (4 4 (:LINEAR *-WEAKLY-MONOTONIC . 1))
        (4 4
           (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 2))
        (4 4
           (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 1))
        (4 4 (:LINEAR *-STRONGLY-MONOTONIC . 2))
        (4 4 (:LINEAR *-STRONGLY-MONOTONIC . 1))
        (2 2 (:REWRITE DEFAULT-<-2))
        (2 2 (:REWRITE DEFAULT-<-1)))
(EXPT-POS (17 8 (:REWRITE DEFAULT-<-2))
          (15 5 (:REWRITE DEFAULT-*-2))
          (12 4 (:REWRITE COMMUTATIVITY-OF-+))
          (8 8 (:REWRITE DEFAULT-<-1))
          (8 8 (:REWRITE DEFAULT-+-2))
          (8 8 (:REWRITE DEFAULT-+-1))
          (5 5 (:REWRITE DEFAULT-*-1))
          (3 3 (:REWRITE ZIP-OPEN)))
(EXPT-MONOTONE-1 (357 99 (:REWRITE DEFAULT-*-2))
                 (246 137 (:REWRITE DEFAULT-<-1))
                 (215 215 (:REWRITE DEFAULT-+-2))
                 (215 215 (:REWRITE DEFAULT-+-1))
                 (184 137 (:REWRITE DEFAULT-<-2))
                 (99 99 (:REWRITE DEFAULT-*-1))
                 (34 34 (:REWRITE FOLD-CONSTS-IN-+)))
(EXPT-MONOTONE (109 109 (:TYPE-PRESCRIPTION A14 . 1))
               (46 2 (:DEFINITION EXPT))
               (16 6 (:REWRITE DEFAULT-*-2))
               (13 13 (:REWRITE DEFAULT-+-2))
               (13 13 (:REWRITE DEFAULT-+-1))
               (7 4 (:REWRITE DEFAULT-<-2))
               (7 4 (:REWRITE DEFAULT-<-1))
               (6 6 (:REWRITE DEFAULT-*-1))
               (2 2 (:REWRITE ZIP-OPEN))
               (1 1 (:REWRITE A4)))
(EXPT-STRONG-MONOTONE-1 (366 102 (:REWRITE DEFAULT-*-2))
                        (252 143 (:REWRITE DEFAULT-<-2))
                        (219 219 (:REWRITE DEFAULT-+-2))
                        (219 219 (:REWRITE DEFAULT-+-1))
                        (190 143 (:REWRITE DEFAULT-<-1))
                        (102 102 (:REWRITE DEFAULT-*-1))
                        (34 34 (:REWRITE FOLD-CONSTS-IN-+)))
(EXPT-STRONG-MONOTONE-2 (109 109 (:TYPE-PRESCRIPTION A14 . 1))
                        (46 2 (:DEFINITION EXPT))
                        (16 6 (:REWRITE DEFAULT-*-2))
                        (13 13 (:REWRITE DEFAULT-+-2))
                        (13 13 (:REWRITE DEFAULT-+-1))
                        (7 4 (:REWRITE DEFAULT-<-2))
                        (7 4 (:REWRITE DEFAULT-<-1))
                        (6 6 (:REWRITE DEFAULT-*-1))
                        (2 2 (:REWRITE ZIP-OPEN))
                        (1 1 (:REWRITE A4)))
(EXPT-STRONG-MONOTONE (464 464 (:TYPE-PRESCRIPTION A14 . 1))
                      (414 18 (:DEFINITION EXPT))
                      (126 36 (:REWRITE DEFAULT-*-2))
                      (108 36 (:REWRITE COMMUTATIVITY-OF-+))
                      (72 72 (:REWRITE DEFAULT-+-2))
                      (72 72 (:REWRITE DEFAULT-+-1))
                      (63 36 (:REWRITE DEFAULT-<-2))
                      (63 36 (:REWRITE DEFAULT-<-1))
                      (36 36 (:REWRITE DEFAULT-*-1))
                      (18 18 (:REWRITE ZIP-OPEN)))
(EXPT- (567 198 (:REWRITE DEFAULT-*-2))
       (327 327 (:REWRITE DEFAULT-+-2))
       (327 327 (:REWRITE DEFAULT-+-1))
       (316 62 (:REWRITE ZIP-OPEN))
       (257 198 (:REWRITE DEFAULT-*-1))
       (254 20
            (:REWRITE REARRANGE-NEGATIVE-COEFS-EQUAL))
       (139 21 (:REWRITE DEFAULT-UNARY-/))
       (76 76 (:REWRITE DEFAULT-<-2))
       (76 76 (:REWRITE DEFAULT-<-1))
       (35 35 (:REWRITE FOLD-CONSTS-IN-+))
       (30 30
           (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 2))
       (30 30
           (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 1))
       (30 30 (:LINEAR *-WEAKLY-MONOTONIC . 2))
       (30 30 (:LINEAR *-WEAKLY-MONOTONIC . 1))
       (30 30
           (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 2))
       (30 30
           (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 1))
       (30 30 (:LINEAR *-STRONGLY-MONOTONIC . 2))
       (30 30 (:LINEAR *-STRONGLY-MONOTONIC . 1))
       (10 10 (:REWRITE A5))
       (8 8 (:LINEAR /-WEAKLY-MONOTONIC))
       (8 8 (:LINEAR /-STRONGLY-MONOTONIC)))
(EXPT-NON-NEG (17 8 (:REWRITE DEFAULT-<-1))
              (15 5 (:REWRITE DEFAULT-*-2))
              (12 4 (:REWRITE COMMUTATIVITY-OF-+))
              (8 8 (:REWRITE DEFAULT-<-2))
              (8 8 (:REWRITE DEFAULT-+-2))
              (8 8 (:REWRITE DEFAULT-+-1))
              (5 5 (:REWRITE DEFAULT-*-1))
              (3 3 (:REWRITE ZIP-OPEN)))
(EXPO+ (12 12 (:TYPE-PRESCRIPTION A14 . 1)))
(EXP+1-1 (169 7 (:DEFINITION EXPT))
         (54 16 (:REWRITE DEFAULT-*-2))
         (35 32 (:REWRITE DEFAULT-+-2))
         (35 32 (:REWRITE DEFAULT-+-1))
         (20 11 (:REWRITE DEFAULT-<-2))
         (19 16 (:REWRITE DEFAULT-*-1))
         (17 11 (:REWRITE DEFAULT-<-1))
         (16 4 (:REWRITE A4))
         (7 7 (:REWRITE ZIP-OPEN))
         (4 2 (:REWRITE UNICITY-OF-0))
         (2 2 (:DEFINITION FIX)))
(EXP+1 (323 323 (:TYPE-PRESCRIPTION A14 . 1))
       (200 8 (:DEFINITION EXPT))
       (89 50 (:REWRITE DEFAULT-+-2))
       (79 24 (:REWRITE DEFAULT-*-2))
       (68 50 (:REWRITE DEFAULT-+-1))
       (31 13 (:REWRITE DEFAULT-<-2))
       (30 24 (:REWRITE DEFAULT-*-1))
       (28 16 (:REWRITE A4))
       (16 13 (:REWRITE DEFAULT-<-1))
       (9 9 (:REWRITE FOLD-CONSTS-IN-+))
       (8 8 (:REWRITE ZIP-OPEN))
       (4 2 (:REWRITE UNICITY-OF-0))
       (2 2
          (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                   . 2))
       (2 2
          (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                   . 1))
       (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 2))
       (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 1))
       (2 2
          (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                   . 2))
       (2 2
          (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                   . 1))
       (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 2))
       (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 1)))
(EXP+2-1 (360 360 (:TYPE-PRESCRIPTION A14 . 1))
         (291 13 (:DEFINITION EXPT))
         (84 24 (:REWRITE DEFAULT-*-2))
         (55 55 (:REWRITE DEFAULT-+-2))
         (55 55 (:REWRITE DEFAULT-+-1))
         (31 2
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 2))
         (30 24 (:REWRITE DEFAULT-*-1))
         (28 19 (:REWRITE DEFAULT-<-1))
         (25 19 (:REWRITE DEFAULT-<-2))
         (15 15 (:REWRITE A4))
         (14 14 (:REWRITE FOLD-CONSTS-IN-+))
         (13 13 (:REWRITE ZIP-OPEN))
         (2 2
            (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                     . 2))
         (2 2
            (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                     . 1))
         (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 2))
         (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 1))
         (2 2
            (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                     . 1))
         (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 1)))
(EXP+2-2 (600 600 (:TYPE-PRESCRIPTION A14 . 1))
         (230 12 (:DEFINITION EXPT))
         (70 19 (:REWRITE DEFAULT-*-2))
         (62 18 (:REWRITE COMMUTATIVITY-OF-+))
         (49 40 (:REWRITE DEFAULT-+-2))
         (46 40 (:REWRITE DEFAULT-+-1))
         (35 20 (:REWRITE DEFAULT-<-2))
         (29 20 (:REWRITE DEFAULT-<-1))
         (19 19 (:REWRITE DEFAULT-*-1))
         (12 12 (:REWRITE ZIP-OPEN))
         (5 5 (:REWRITE FOLD-CONSTS-IN-+))
         (5 5 (:REWRITE A4))
         (2 2
            (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                     . 2))
         (2 2
            (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                     . 1))
         (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 2))
         (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 1))
         (2 2
            (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                     . 2))
         (2 2
            (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                     . 1))
         (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 2))
         (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 1)))
(EXP+2-3 (463 463 (:TYPE-PRESCRIPTION A14 . 1))
         (300 17 (:DEFINITION EXPT))
         (92 29 (:REWRITE DEFAULT-*-2))
         (77 23 (:REWRITE COMMUTATIVITY-OF-+))
         (70 52 (:REWRITE DEFAULT-+-2))
         (58 52 (:REWRITE DEFAULT-+-1))
         (35 26 (:REWRITE DEFAULT-<-2))
         (32 26 (:REWRITE DEFAULT-<-1))
         (29 29 (:REWRITE DEFAULT-*-1))
         (17 17 (:REWRITE ZIP-OPEN))
         (6 6 (:REWRITE FOLD-CONSTS-IN-+))
         (6 6 (:REWRITE A4))
         (2 2
            (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                     . 2))
         (2 2
            (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                     . 1))
         (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 2))
         (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 1))
         (2 2
            (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                     . 2))
         (2 2
            (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                     . 1))
         (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 2))
         (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 1)))
(EXP+2 (245 12 (:DEFINITION EXPT))
       (107 56 (:REWRITE DEFAULT-+-2))
       (89 25 (:REWRITE DEFAULT-*-2))
       (74 56 (:REWRITE DEFAULT-+-1))
       (36 18 (:REWRITE DEFAULT-<-1))
       (31 25 (:REWRITE DEFAULT-*-1))
       (24 18 (:REWRITE DEFAULT-<-2))
       (22 14 (:REWRITE A4))
       (12 12 (:REWRITE ZIP-OPEN))
       (8 8 (:REWRITE FOLD-CONSTS-IN-+))
       (2 2
          (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                   . 2))
       (2 2
          (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                   . 1))
       (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 2))
       (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 1))
       (2 2
          (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                   . 2))
       (2 2
          (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                   . 1))
       (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 2))
       (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 1)))
(EXP-INVERT-1 (167 47 (:REWRITE DEFAULT-*-2))
              (72 72 (:REWRITE DEFAULT-+-2))
              (72 72 (:REWRITE DEFAULT-+-1))
              (71 47 (:REWRITE DEFAULT-*-1))
              (42 4
                  (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                           . 2))
              (41 29 (:REWRITE DEFAULT-<-2))
              (38 29 (:REWRITE DEFAULT-<-1))
              (16 16 (:REWRITE ZIP-OPEN))
              (4 4
                 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                          . 2))
              (4 4
                 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                          . 1))
              (4 4 (:LINEAR *-WEAKLY-MONOTONIC . 2))
              (4 4 (:LINEAR *-WEAKLY-MONOTONIC . 1))
              (4 4
                 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                          . 1))
              (4 4 (:LINEAR *-STRONGLY-MONOTONIC . 1)))
(EXP-INVERT-2 (115 31 (:REWRITE DEFAULT-*-2))
              (90 51 (:REWRITE DEFAULT-+-2))
              (63 51 (:REWRITE DEFAULT-+-1))
              (40 31 (:REWRITE DEFAULT-*-1))
              (38 16 (:REWRITE A4))
              (23 17 (:REWRITE DEFAULT-<-2))
              (23 17 (:REWRITE DEFAULT-<-1))
              (9 9 (:REWRITE ZIP-OPEN))
              (2 2 (:REWRITE FOLD-CONSTS-IN-+))
              (2 2
                 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                          . 2))
              (2 2
                 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                          . 1))
              (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 2))
              (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 1))
              (2 2
                 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                          . 2))
              (2 2
                 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                          . 1))
              (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 2))
              (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 1)))
(CANCEL-X (4 2
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 2))
          (4 2 (:LINEAR *-STRONGLY-MONOTONIC . 2))
          (2 2 (:REWRITE DEFAULT-<-2))
          (2 2 (:REWRITE DEFAULT-<-1))
          (2 2 (:LINEAR /-WEAKLY-MONOTONIC))
          (2 2 (:LINEAR /-STRONGLY-MONOTONIC))
          (2 2
             (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 2))
          (2 2
             (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 1))
          (2 2
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 1))
          (1 1 (:REWRITE DEFAULT-*-2))
          (1 1 (:REWRITE DEFAULT-*-1)))
(EXP-INVERT (874 874 (:TYPE-PRESCRIPTION A14 . 1))
            (308 86 (:REWRITE DEFAULT-*-2))
            (246 3 (:REWRITE DEFAULT-UNARY-/))
            (222 147 (:REWRITE DEFAULT-+-2))
            (171 147 (:REWRITE DEFAULT-+-1))
            (168 3
                 (:REWRITE REARRANGE-NEGATIVE-COEFS-EQUAL))
            (100 38 (:REWRITE A4))
            (98 86 (:REWRITE DEFAULT-*-1))
            (88 61 (:REWRITE DEFAULT-<-2))
            (82 61 (:REWRITE DEFAULT-<-1))
            (69 6
                (:REWRITE REARRANGE-FRACTIONAL-COEFS-EQUAL))
            (27 27 (:REWRITE ZIP-OPEN))
            (2 2 (:REWRITE FOLD-CONSTS-IN-+))
            (2 2 (:LINEAR /-WEAKLY-MONOTONIC))
            (2 2 (:LINEAR /-STRONGLY-MONOTONIC)))
(*-DOUBLY-MONOTONIC)
(SQ-SQ-1 (1717 1717 (:TYPE-PRESCRIPTION A14 . 1))
         (756 351 (:REWRITE DEFAULT-*-2))
         (518 68
              (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 2))
         (489 351 (:REWRITE DEFAULT-*-1))
         (372 68
              (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 1))
         (329 13 (:DEFINITION EXPT))
         (183 67 (:REWRITE DEFAULT-<-1))
         (146 89 (:REWRITE DEFAULT-+-2))
         (125 89 (:REWRITE DEFAULT-+-1))
         (118 118 (:REWRITE A5))
         (89 67 (:REWRITE DEFAULT-<-2))
         (68 68
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 2))
         (68 68
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 1))
         (68 68 (:LINEAR *-STRONGLY-MONOTONIC . 2))
         (68 68 (:LINEAR *-STRONGLY-MONOTONIC . 1))
         (62 22 (:REWRITE A4))
         (20 4 (:REWRITE UNICITY-OF-0))
         (13 13 (:REWRITE ZIP-OPEN)))
(SQRT<= (24 24 (:REWRITE DEFAULT-*-2))
        (24 24 (:REWRITE DEFAULT-*-1))
        (16 14 (:REWRITE DEFAULT-<-2))
        (16 14 (:REWRITE DEFAULT-<-1))
        (8 8
           (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 2))
        (8 8
           (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 1))
        (8 8
           (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 2))
        (8 8
           (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 1)))
(SQ-SQ-2 (1245 1245 (:TYPE-PRESCRIPTION A14 . 1))
         (308 145 (:REWRITE DEFAULT-*-2))
         (284 32
              (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 1))
         (265 10 (:DEFINITION EXPT))
         (192 145 (:REWRITE DEFAULT-*-1))
         (101 32
              (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 2))
         (89 64 (:REWRITE DEFAULT-+-2))
         (82 33 (:REWRITE DEFAULT-<-1))
         (80 64 (:REWRITE DEFAULT-+-1))
         (64 20 (:REWRITE A4))
         (47 47 (:REWRITE A5))
         (47 33 (:REWRITE DEFAULT-<-2))
         (32 32
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 2))
         (32 32
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 1))
         (32 32 (:LINEAR *-STRONGLY-MONOTONIC . 2))
         (32 32 (:LINEAR *-STRONGLY-MONOTONIC . 1))
         (28 8 (:REWRITE UNICITY-OF-0))
         (10 10 (:REWRITE ZIP-OPEN)))
(SQ-SQ-3 (272 272 (:TYPE-PRESCRIPTION A14 . 1))
         (192 12
              (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 1))
         (164 4 (:REWRITE REARRANGE-NEGATIVE-COEFS-<))
         (54 6 (:REWRITE COMMUTATIVITY-OF-+))
         (52 16 (:REWRITE DEFAULT-*-2))
         (33 9 (:DEFINITION FIX))
         (28 16 (:REWRITE DEFAULT-*-1))
         (28 1 (:DEFINITION EXPT))
         (26 14 (:REWRITE DEFAULT-+-2))
         (26 14 (:REWRITE DEFAULT-+-1))
         (25 10 (:REWRITE DEFAULT-<-2))
         (22 10 (:REWRITE DEFAULT-<-1))
         (22 5 (:REWRITE UNICITY-OF-0))
         (20 4 (:REWRITE UNICITY-OF-1))
         (12 12
             (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 2))
         (12 12 (:LINEAR *-WEAKLY-MONOTONIC . 2))
         (12 12
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 2))
         (12 12
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 1))
         (12 12 (:LINEAR *-STRONGLY-MONOTONIC . 2))
         (12 12 (:LINEAR *-STRONGLY-MONOTONIC . 1))
         (8 2 (:REWRITE A4))
         (2 2 (:REWRITE A5))
         (1 1 (:REWRITE ZIP-OPEN)))
(SQ-SQ-4 (5369 5369 (:TYPE-PRESCRIPTION A14 . 1))
         (2080 81 (:DEFINITION EXPT))
         (1715 658 (:REWRITE DEFAULT-*-2))
         (906 658 (:REWRITE DEFAULT-*-1))
         (793 498 (:REWRITE DEFAULT-+-2))
         (622 498 (:REWRITE DEFAULT-+-1))
         (464 208 (:REWRITE DEFAULT-<-1))
         (382 112 (:REWRITE A4))
         (324 34
              (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 1))
         (261 208 (:REWRITE DEFAULT-<-2))
         (125 125 (:REWRITE A5))
         (103 34
              (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 2))
         (81 81 (:REWRITE ZIP-OPEN))
         (78 33 (:REWRITE UNICITY-OF-0))
         (34 34
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 2))
         (34 34
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 1))
         (34 34 (:LINEAR *-STRONGLY-MONOTONIC . 2))
         (34 34 (:LINEAR *-STRONGLY-MONOTONIC . 1)))
(SQ-SQ-5 (558 21 (:DEFINITION EXPT))
         (273 81 (:REWRITE DEFAULT-*-2))
         (103 103 (:REWRITE DEFAULT-+-2))
         (103 103 (:REWRITE DEFAULT-+-1))
         (102 81 (:REWRITE DEFAULT-*-1))
         (77 35 (:REWRITE DEFAULT-<-1))
         (35 35 (:REWRITE DEFAULT-<-2))
         (21 21 (:REWRITE ZIP-OPEN))
         (16 16
             (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 2))
         (16 16
             (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 1))
         (16 16
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 2))
         (16 16
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 1))
         (16 16 (:LINEAR *-STRONGLY-MONOTONIC . 2))
         (16 16 (:LINEAR *-STRONGLY-MONOTONIC . 1))
         (5 5 (:REWRITE A5)))
(SQ-SQ-6 (1304 1304 (:TYPE-PRESCRIPTION A14 . 1))
         (446 18 (:DEFINITION EXPT))
         (379 143 (:REWRITE DEFAULT-*-2))
         (209 143 (:REWRITE DEFAULT-*-1))
         (192 12
              (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 1))
         (184 112 (:REWRITE DEFAULT-+-2))
         (148 112 (:REWRITE DEFAULT-+-1))
         (126 54 (:REWRITE DEFAULT-<-1))
         (74 54 (:REWRITE DEFAULT-<-2))
         (56 16 (:REWRITE A4))
         (28 8 (:REWRITE UNICITY-OF-0))
         (18 18 (:REWRITE ZIP-OPEN))
         (18 18 (:REWRITE A5))
         (12 12
             (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 2))
         (12 12 (:LINEAR *-WEAKLY-MONOTONIC . 2))
         (12 12
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 2))
         (12 12
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 1))
         (12 12 (:LINEAR *-STRONGLY-MONOTONIC . 2))
         (12 12 (:LINEAR *-STRONGLY-MONOTONIC . 1)))
(SQ-SQ-7 (20 12 (:REWRITE DEFAULT-+-1))
         (19 17 (:REWRITE DEFAULT-*-2))
         (17 17 (:REWRITE DEFAULT-*-1))
         (16 12 (:REWRITE DEFAULT-+-2))
         (6 6 (:REWRITE A4))
         (3 1 (:REWRITE DEFAULT-<-1))
         (2 2
            (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                     . 2))
         (2 2
            (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                     . 1))
         (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 2))
         (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 1))
         (2 2
            (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                     . 2))
         (2 2
            (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                     . 1))
         (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 2))
         (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 1))
         (2 1 (:REWRITE DEFAULT-<-2))
         (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(SQ-SQ-8 (885 885 (:TYPE-PRESCRIPTION A14 . 1))
         (310 150 (:REWRITE DEFAULT-*-2))
         (239 10 (:DEFINITION EXPT))
         (210 121 (:REWRITE DEFAULT-+-2))
         (189 121 (:REWRITE DEFAULT-+-1))
         (186 150 (:REWRITE DEFAULT-*-1))
         (152 10
              (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                       . 1))
         (80 35 (:REWRITE DEFAULT-<-1))
         (56 35 (:REWRITE DEFAULT-<-2))
         (49 37 (:REWRITE A4))
         (10 10 (:REWRITE ZIP-OPEN))
         (10 10
             (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 2))
         (10 10 (:LINEAR *-WEAKLY-MONOTONIC . 2))
         (10 10
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 2))
         (10 10
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 1))
         (10 10 (:LINEAR *-STRONGLY-MONOTONIC . 2))
         (10 10 (:LINEAR *-STRONGLY-MONOTONIC . 1))
         (8 8 (:REWRITE FOLD-CONSTS-IN-+)))
(SQ-SQ-9 (302 94 (:REWRITE DEFAULT-*-2))
         (185 108 (:REWRITE DEFAULT-+-2))
         (117 108 (:REWRITE DEFAULT-+-1))
         (103 94 (:REWRITE DEFAULT-*-1))
         (34 34
             (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 2))
         (34 34
             (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 1))
         (34 34 (:LINEAR *-WEAKLY-MONOTONIC . 2))
         (34 34 (:LINEAR *-WEAKLY-MONOTONIC . 1))
         (34 34
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 2))
         (34 34
             (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                      . 1))
         (34 34 (:LINEAR *-STRONGLY-MONOTONIC . 2))
         (34 34 (:LINEAR *-STRONGLY-MONOTONIC . 1))
         (24 24 (:REWRITE DEFAULT-<-2))
         (24 24 (:REWRITE DEFAULT-<-1))
         (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(SQ-SQ (1107 1107 (:TYPE-PRESCRIPTION A14 . 1))
       (502 184 (:REWRITE DEFAULT-*-2))
       (462 19 (:DEFINITION EXPT))
       (367 173 (:REWRITE DEFAULT-+-2))
       (255 173 (:REWRITE DEFAULT-+-1))
       (247 184 (:REWRITE DEFAULT-*-1))
       (141 12
            (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                     . 1))
       (80 44 (:REWRITE A4))
       (75 37 (:REWRITE DEFAULT-<-1))
       (55 37 (:REWRITE DEFAULT-<-2))
       (28 8 (:REWRITE UNICITY-OF-0))
       (19 19 (:REWRITE ZIP-OPEN))
       (12 12
           (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 2))
       (12 12 (:LINEAR *-WEAKLY-MONOTONIC . 2))
       (12 12
           (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 2))
       (12 12
           (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                    . 1))
       (12 12 (:LINEAR *-STRONGLY-MONOTONIC . 2))
       (12 12 (:LINEAR *-STRONGLY-MONOTONIC . 1))
       (11 11 (:REWRITE FOLD-CONSTS-IN-+)))
