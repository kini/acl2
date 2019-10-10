; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "JAVA" (append *std-pkg-symbols*
                       '(*pkg-witness-name*
                         *primitive-formals-and-guards*
                         add-const-to-untranslate-preprocess
                         add-suffix
                         all-ffn-symbs
                         all-free/bound-vars
                         all-vars-open
                         all-vars-open-lst
                         alpha/digit-chars
                         alpha/digit/dash-charlist-p
                         alpha/digit/uscore/dollar-charlist-p
                         alpha/uscore/dollar-char-p
                         bad-atom<=
                         body
                         bool
                         char-downcase
                         char-upcase
                         chars=>nats
                         defxdoc+
                         doublets-to-alist
                         dumb-occur-var-open
                         dumb-occur-var-open-lst
                         ensure-boolean$
                         ensure-doublet-list$
                         ensure-function-name$
                         ensure-function-name-list$
                         ensure-list-functions$
                         ensure-list-no-duplicates$
                         ensure-member-of-list$
                         ensure-string$
                         ensure-string-or-nil$
                         ensure-term$
                         ensure-term-ground$
                         er-soft+
                         explode
                         fargn
                         fargs
                         fcons-term
                         fcons-term*
                         ffn-symb
                         flambda-applicationp
                         flambdap
                         flatten
                         fmt-hard-right-margin
                         fmt-soft-right-margin
                         formals
                         fquotep
                         implode
                         impossible
                         known-packages
                         lambda-body
                         lambda-formals
                         logic-fns-with-raw-code
                         lower-case-p
                         make-lambda
                         maybe-stringp
                         msg-listp
                         nats=>string
                         no-stobjs-p
                         organize-symbols-by-name
                         organize-symbols-by-pkg
                         packn-pos
                         partition-rest-and-keyword-args
                         patbind-fun
                         patbind-run-when
                         primitivep
                         printable-charlist-p
                         program-fns-with-raw-code
                         pseudo-termfnp
                         pure-raw-p
                         quote-listp
                         rawp
                         remove-assocs-eq
                         remove-mbe-exec
                         remove-mbe-logic
                         remove-progn
                         remove-trivial-vars
                         remove-unused-vars
                         sbyte16
                         sbyte32
                         sbyte64
                         sbyte8
                         sort-symbol-listp
                         str-fix
                         string-downcase
                         string-string-alistp
                         string-symbollist-alistp
                         string-upcase
                         string=>nats
                         symbol-name-lst
                         symbol-pos-alistp
                         symbol-string-alistp
                         symbol-symbol-alistp
                         symbol-package-name-lst
                         trans-eval
                         tuplep
                         typed-tuplep
                         ubody
                         ubyte16
                         ubyte8=>hexchars
                         ubyte8s=>hexstring
                         unnormalized-body
                         unquote-term
                         unquote-term-list
                         unsigned-byte-listp
                         upper-case-p
                         variablep
                         str::chars-in-charset-p
                         str::natstr)))
