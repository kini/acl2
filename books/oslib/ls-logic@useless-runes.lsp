(OSLIB::REMOVE-NONSTRINGS)
(OSLIB::STRING-LISTP-OF-REMOVE-NONSTRINGS (24 23 (:REWRITE DEFAULT-CAR))
                                          (17 16 (:REWRITE DEFAULT-CDR)))
(OSLIB::LS-FN)
(OSLIB::STRING-LISTP-OF-LS.VAL (3 1 (:DEFINITION STRING-LISTP))
                               (1 1 (:REWRITE DEFAULT-CDR))
                               (1 1 (:REWRITE DEFAULT-CAR)))
(OSLIB::STATE-P1-OF-LS.STATE
     (12 4
         (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
     (8 2 (:DEFINITION STATE-P))
     (4 4 (:TYPE-PRESCRIPTION STATE-P)))
(OSLIB::LS!-FN)
(OSLIB::STRING-LISTP-OF-LS!.VAL (3 1 (:DEFINITION STRING-LISTP))
                                (1 1 (:REWRITE DEFAULT-CDR))
                                (1 1 (:REWRITE DEFAULT-CAR)))
(OSLIB::STATE-P1-OF-LS!.STATE
     (12 4
         (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
     (8 2 (:DEFINITION STATE-P))
     (4 4 (:TYPE-PRESCRIPTION STATE-P)))
(OSLIB::LS-FILES-AUX
     (6 6 (:REWRITE DEFAULT-CDR))
     (6 2
        (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
     (5 5 (:REWRITE DEFAULT-CAR))
     (1 1 (:REWRITE STR-FIX-WHEN-STRINGP))
     (1 1 (:REWRITE STR-FIX-DEFAULT))
     (1 1
        (:REWRITE CAR-OF-STRING-LIST-FIX-X-NORMALIZE-CONST-UNDER-STREQV)))
(OSLIB::STRING-LISTP-OF-LS-FILES-AUX.REGULAR
     (51 51 (:REWRITE DEFAULT-CAR))
     (30 30 (:REWRITE STR-FIX-WHEN-STRINGP))
     (30 30 (:REWRITE STR-FIX-DEFAULT))
     (30 30
         (:REWRITE CAR-OF-STRING-LIST-FIX-X-NORMALIZE-CONST-UNDER-STREQV))
     (26 26 (:REWRITE DEFAULT-CDR)))
(OSLIB::STATE-P1-OF-LS-FILES-AUX.STATE
     (39 39 (:REWRITE STR-FIX-WHEN-STRINGP))
     (39 39 (:REWRITE STR-FIX-DEFAULT))
     (39 39 (:REWRITE DEFAULT-CAR))
     (39 39
         (:REWRITE CAR-OF-STRING-LIST-FIX-X-NORMALIZE-CONST-UNDER-STREQV))
     (5 5 (:REWRITE DEFAULT-CDR)))
(OSLIB::LS-FILES-FN)
(OSLIB::STRING-LISTP-OF-LS-FILES.REGULAR (3 1 (:DEFINITION STRING-LISTP))
                                         (1 1 (:REWRITE DEFAULT-CDR))
                                         (1 1 (:REWRITE DEFAULT-CAR)))
(OSLIB::STATE-P1-OF-LS-FILES.STATE
     (12 4
         (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
     (8 2 (:DEFINITION STATE-P))
     (4 4 (:TYPE-PRESCRIPTION STATE-P)))
(OSLIB::LS-FILES!-FN)
(OSLIB::STRING-LISTP-OF-LS-FILES!.VAL (3 1 (:DEFINITION STRING-LISTP))
                                      (1 1 (:REWRITE DEFAULT-CDR))
                                      (1 1 (:REWRITE DEFAULT-CAR)))
(OSLIB::STATE-P1-OF-LS-FILES!.STATE
     (12 4
         (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
     (8 2 (:DEFINITION STATE-P))
     (4 4 (:TYPE-PRESCRIPTION STATE-P)))
(OSLIB::LS-SUBDIRS-AUX
     (6 6 (:REWRITE DEFAULT-CDR))
     (6 2
        (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
     (5 5 (:REWRITE DEFAULT-CAR))
     (1 1 (:REWRITE STR-FIX-WHEN-STRINGP))
     (1 1 (:REWRITE STR-FIX-DEFAULT))
     (1 1
        (:REWRITE CAR-OF-STRING-LIST-FIX-X-NORMALIZE-CONST-UNDER-STREQV)))
(OSLIB::STRING-LISTP-OF-LS-SUBDIRS-AUX.SUBDIRS
     (51 51 (:REWRITE DEFAULT-CAR))
     (30 30 (:REWRITE STR-FIX-WHEN-STRINGP))
     (30 30 (:REWRITE STR-FIX-DEFAULT))
     (30 30
         (:REWRITE CAR-OF-STRING-LIST-FIX-X-NORMALIZE-CONST-UNDER-STREQV))
     (26 26 (:REWRITE DEFAULT-CDR)))
(OSLIB::STATE-P1-OF-LS-SUBDIRS-AUX.STATE
     (39 39 (:REWRITE STR-FIX-WHEN-STRINGP))
     (39 39 (:REWRITE STR-FIX-DEFAULT))
     (39 39 (:REWRITE DEFAULT-CAR))
     (39 39
         (:REWRITE CAR-OF-STRING-LIST-FIX-X-NORMALIZE-CONST-UNDER-STREQV))
     (5 5 (:REWRITE DEFAULT-CDR)))
(OSLIB::LS-SUBDIRS-FN)
(OSLIB::STRING-LISTP-OF-LS-SUBDIRS.SUBDIRS (3 1 (:DEFINITION STRING-LISTP))
                                           (1 1 (:REWRITE DEFAULT-CDR))
                                           (1 1 (:REWRITE DEFAULT-CAR)))
(OSLIB::STATE-P1-OF-LS-SUBDIRS.STATE
     (12 4
         (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
     (8 2 (:DEFINITION STATE-P))
     (4 4 (:TYPE-PRESCRIPTION STATE-P)))
(OSLIB::LS-SUBDIRS!-FN)
(OSLIB::STRING-LISTP-OF-LS-SUBDIRS!.VAL (3 1 (:DEFINITION STRING-LISTP))
                                        (1 1 (:REWRITE DEFAULT-CDR))
                                        (1 1 (:REWRITE DEFAULT-CAR)))
(OSLIB::STATE-P1-OF-LS-SUBDIRS!.STATE
     (12 4
         (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
     (8 2 (:DEFINITION STATE-P))
     (4 4 (:TYPE-PRESCRIPTION STATE-P)))
