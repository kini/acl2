(ALISTP-OF-CONS (3 3 (:REWRITE DEFAULT-CDR))
                (3 3 (:REWRITE DEFAULT-CAR)))
(ALISTP-OF-APPEND (32 16
                      (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                  (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP))
                  (16 16 (:TYPE-PRESCRIPTION BINARY-APPEND))
                  (16 16 (:REWRITE DEFAULT-CAR))
                  (12 12 (:REWRITE DEFAULT-CDR)))
(ALISTP-OF-UNION-EQUAL (62 62 (:REWRITE DEFAULT-CAR))
                       (54 54 (:REWRITE DEFAULT-CDR))
                       (48 24 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
                       (24 24 (:TYPE-PRESCRIPTION BOOLEANP)))
(CONSP-OF-NTH-WHEN-ALISTP (229 130 (:REWRITE DEFAULT-+-2))
                          (192 192 (:REWRITE DEFAULT-CDR))
                          (154 106 (:REWRITE DEFAULT-<-2))
                          (130 130 (:REWRITE DEFAULT-+-1))
                          (119 106 (:REWRITE DEFAULT-<-1))
                          (88 88 (:REWRITE DEFAULT-CAR))
                          (33 18 (:REWRITE ZP-OPEN))
                          (32 32
                              (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                          (15 5 (:REWRITE FOLD-CONSTS-IN-+)))
(CONSP-OF-NTH-WHEN-ALISTP-CHEAP
     (229 130 (:REWRITE DEFAULT-+-2))
     (192 192 (:REWRITE DEFAULT-CDR))
     (154 106 (:REWRITE DEFAULT-<-2))
     (130 130 (:REWRITE DEFAULT-+-1))
     (119 106 (:REWRITE DEFAULT-<-1))
     (88 88 (:REWRITE DEFAULT-CAR))
     (33 18 (:REWRITE ZP-OPEN))
     (32 32
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (15 5 (:REWRITE FOLD-CONSTS-IN-+)))
(ALISTP-OF-CDR (1 1 (:REWRITE DEFAULT-CDR))
               (1 1 (:REWRITE DEFAULT-CAR)))
(CONSP-OF-CAR-WHEN-ALISTP (4 1 (:REWRITE ALISTP-OF-CDR))
                          (3 3 (:REWRITE DEFAULT-CAR))
                          (1 1 (:REWRITE DEFAULT-CDR)))
