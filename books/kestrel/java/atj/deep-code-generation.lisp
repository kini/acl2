; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "common-code-generation")
(include-book "pre-translation")

(include-book "kestrel/std/system/pseudo-termfnp" :dir :system)
(include-book "kestrel/std/system/ubody" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-deep-code-generation
  :parents (atj-code-generation)
  :short "Code generation that is specific to the deep embedding approach."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-deep-qconst
  ((qconst "(Unquoted) value of the ACL2 quoted constant.")
   (jvar-value-base stringp)
   (jvar-value-index posp))
  :returns (mv (block jblockp)
               (expr jexprp)
               (new-jvar-value-index posp :hyp (posp jvar-value-index)))
  :short "Generate Java code to build a deeply embedded ACL2 quoted constant."
  (b* (((mv value-block
            value-expr
            jvar-value-index) (atj-gen-value qconst
                                             jvar-value-base
                                             jvar-value-index))
       (block value-block)
       (expr (jexpr-smethod *aij-type-qconst*
                            "make"
                            (list value-expr))))
    (mv block expr jvar-value-index)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-deep-var ((var symbolp "The ACL2 variable."))
  :returns (expr jexprp)
  :short "Generate Java code to build a deeply embedded ACL2 variable."
  (jexpr-smethod *aij-type-var*
                 "make"
                 (list (atj-gen-symbol var))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-deep-formals ((formals symbol-listp))
  :returns (expr jexprp)
  :short "Generate Java code to build a deeply embedded formals parameter list
          of an ACL2 named function or lambda expression."
  :long
  (xdoc::topstring-p
   "The generated code builds an array of the formals as symbols.")
  (jexpr-newarray-init *aij-type-symbol*
                       (atj-gen-symbols formals)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-gen-deep-term-fns
  :short "Functions to generate Java code to build deeply embedded ACL2 terms."

  (define atj-gen-deep-fnapp ((fn pseudo-termfnp)
                              (args pseudo-term-listp)
                              (jvar-value-base stringp)
                              (jvar-value-index posp)
                              (jvar-term-base stringp)
                              (jvar-term-index posp)
                              (jvar-lambda-base stringp)
                              (jvar-lambda-index posp)
                              (guards$ booleanp))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index))
                 (new-jvar-term-index posp :hyp (posp jvar-term-index))
                 (new-jvar-lambda-index posp :hyp (posp jvar-lambda-index)))
    :parents (atj-code-generation atj-gen-deep-term-fns)
    :short "Generate Java code to build
            a deeply embedded ACL2 function application."
    :long
    (xdoc::topstring
     (xdoc::p
      "The generated code
       builds the named function or lambda expression,
       builds the argument terms,
       puts them into an array,
       builds the application,
       puts it to a local variable,
       and returns the local variable.")
     (xdoc::p
      "Terms of the form @('(if a a b)') are treated as @('(or a b)'),
       i.e. the generated code builds a term of the form @('(or a b)').
       In ACL2, @(tsee or) is a macro:
       an untranslated term @('(or a b)') is translated to @('(if a a b)'),
       which, if executed as such by AIJ, would evaluate @('a') twice.
       (ACL2 relies on the underlying Lisp platform to optimize this situation.)
       AIJ provides support for a ``pseudo-function'' @('or')
       that evaluates its arguments non-strictly;
       see the documentation of AIJ for details.
       Thus, ATJ recognizes (translated) terms of the form @('(if a a b)'),
       which are likely derived from @('(or a b)'),
       and represents them in AIJ via the @('or') pseudo-function."))
    (b* (((mv fn args)
          (if (and (eq fn 'if)
                   (= (len args) 3)
                   (equal (first args) (second args)))
              (mv 'or (list (first args) (third args)))
            (mv fn args)))
         ((mv fn-block
              fn-expr
              jvar-value-index
              jvar-term-index
              jvar-lambda-index)
          (if (symbolp fn)
              (mv nil
                  (jexpr-smethod *aij-type-named-fn*
                                 "make"
                                 (list (atj-gen-symbol fn)))
                  jvar-value-index
                  jvar-term-index
                  jvar-lambda-index)
            (atj-gen-deep-lambda (lambda-formals fn)
                                 (lambda-body fn)
                                 jvar-value-base
                                 jvar-value-index
                                 jvar-term-base
                                 jvar-term-index
                                 jvar-lambda-base
                                 jvar-lambda-index
                                 guards$)))
         ((mv args-block
              arg-exprs
              jvar-value-index
              jvar-term-index
              jvar-lambda-index) (atj-gen-deep-terms args
                                                     jvar-value-base
                                                     jvar-value-index
                                                     jvar-term-base
                                                     jvar-term-index
                                                     jvar-lambda-base
                                                     jvar-lambda-index
                                                     guards$))
         (args-expr (jexpr-newarray-init *aij-type-term* arg-exprs))
         (fnapp-expr (jexpr-smethod *aij-type-fn-app*
                                    "make"
                                    (list fn-expr
                                          args-expr)))
         ((mv fnapp-locvar-block
              fnapp-jvar
              jvar-term-index) (atj-gen-jlocvar-indexed *aij-type-term*
                                                        jvar-term-base
                                                        jvar-term-index
                                                        fnapp-expr)))
      (mv (append fn-block
                  args-block
                  fnapp-locvar-block)
          (jexpr-name fnapp-jvar)
          jvar-value-index
          jvar-term-index
          jvar-lambda-index))
    ;; 2nd component is greater then the one of ATJ-GEN-DEEP-LAMBDA
    ;; so that the call of ATJ-GEN-DEEP-LAMBDA decreases
    ;; even when FN is a non-symbol atom (impossible under the guard):
    :measure (two-nats-measure (+ (acl2-count fn) (acl2-count args)) 2))

  (define atj-gen-deep-lambda ((formals symbol-listp)
                               (body pseudo-termp)
                               (jvar-value-base stringp)
                               (jvar-value-index posp)
                               (jvar-term-base stringp)
                               (jvar-term-index posp)
                               (jvar-lambda-base stringp)
                               (jvar-lambda-index posp)
                               (guards$ booleanp))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index))
                 (new-jvar-term-index posp :hyp (posp jvar-term-index))
                 (new-jvar-lambda-index posp :hyp (posp jvar-lambda-index)))
    :parents (atj-code-generation atj-gen-deep-term-fns)
    :short "Generate Java code to build
            a deeply embedded ACL2 lambda expression."
    :long
    (xdoc::topstring-p
     "The generated code
      puts the formals into an array,
      builds the body,
      builds the lambda expression,
      puts it to a local variable,
      and returns the local variable.")
    (b* ((formals-expr (atj-gen-deep-formals formals))
         ((mv body-block
              body-expr
              jvar-value-index
              jvar-term-index
              jvar-lambda-index) (atj-gen-deep-term body
                                                    jvar-value-base
                                                    jvar-value-index
                                                    jvar-term-base
                                                    jvar-term-index
                                                    jvar-lambda-base
                                                    jvar-lambda-index
                                                    guards$))
         (lambda-expr (jexpr-smethod *aij-type-lambda*
                                     "make"
                                     (list formals-expr
                                           body-expr)))
         ((mv lambda-locvar-block
              lambda-jvar
              jvar-lambda-index) (atj-gen-jlocvar-indexed
                                  *aij-type-lambda*
                                  jvar-lambda-base
                                  jvar-lambda-index
                                  lambda-expr)))
      (mv (append body-block
                  lambda-locvar-block)
          (jexpr-name lambda-jvar)
          jvar-value-index
          jvar-term-index
          jvar-lambda-index))
    ;; 2nd component is non-0
    ;; so that the call of ATJ-GEN-DEEP-TERM decreases:
    :measure (two-nats-measure (acl2-count body) 1))

  (define atj-gen-deep-term ((term pseudo-termp)
                             (jvar-value-base stringp)
                             (jvar-value-index posp)
                             (jvar-term-base stringp)
                             (jvar-term-index posp)
                             (jvar-lambda-base stringp)
                             (jvar-lambda-index posp)
                             (guards$ booleanp))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index))
                 (new-jvar-term-index posp :hyp (posp jvar-term-index))
                 (new-jvar-lambda-index posp :hyp (posp jvar-lambda-index)))
    :parents (atj-code-generation atj-gen-deep-term-fns)
    :short "Generate Java code to build a deeply embedded ACL2 term."
    (cond ((variablep term) (mv nil
                                (atj-gen-deep-var term)
                                jvar-value-index
                                jvar-term-index
                                jvar-lambda-index))
          ((fquotep term) (b* (((mv block
                                    expr
                                    jvar-value-index)
                                (atj-gen-deep-qconst (unquote term)
                                                     jvar-value-base
                                                     jvar-value-index)))
                            (mv block
                                expr
                                jvar-value-index
                                jvar-term-index
                                jvar-lambda-index)))
          (t (atj-gen-deep-fnapp (ffn-symb term)
                                 (fargs term)
                                 jvar-value-base
                                 jvar-value-index
                                 jvar-term-base
                                 jvar-term-index
                                 jvar-lambda-base
                                 jvar-lambda-index
                                 guards$)))
    :measure (two-nats-measure (acl2-count term) 0))

  (define atj-gen-deep-terms ((terms pseudo-term-listp)
                              (jvar-value-base stringp)
                              (jvar-value-index posp)
                              (jvar-term-base stringp)
                              (jvar-term-index posp)
                              (jvar-lambda-base stringp)
                              (jvar-lambda-index posp)
                              (guards$ booleanp))
    :returns (mv (block jblockp)
                 (exprs jexpr-listp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index))
                 (new-jvar-term-index posp :hyp (posp jvar-term-index))
                 (new-jvar-lambda-index posp :hyp (posp jvar-lambda-index)))
    :parents (atj-code-generation atj-gen-deep-term-fns)
    :short "Lift @(tsee atj-gen-deep-term) to lists."
    (if (endp terms)
        (mv nil
            nil
            jvar-value-index
            jvar-term-index
            jvar-lambda-index)
      (b* (((mv first-block
                expr
                jvar-value-index
                jvar-term-index
                jvar-lambda-index) (atj-gen-deep-term (car terms)
                                                      jvar-value-base
                                                      jvar-value-index
                                                      jvar-term-base
                                                      jvar-term-index
                                                      jvar-lambda-base
                                                      jvar-lambda-index
                                                      guards$))
           ((mv rest-block
                exprs
                jvar-value-index
                jvar-term-index
                jvar-lambda-index) (atj-gen-deep-terms (cdr terms)
                                                       jvar-value-base
                                                       jvar-value-index
                                                       jvar-term-base
                                                       jvar-term-index
                                                       jvar-lambda-base
                                                       jvar-lambda-index
                                                       guards$)))
        (mv (append first-block
                    rest-block)
            (cons expr exprs)
            jvar-value-index
            jvar-term-index
            jvar-lambda-index)))
    :measure (two-nats-measure (acl2-count terms) 0))

  :hints (("Goal" :in-theory (enable len))) ; for termination

  :prepwork ((local (in-theory (disable posp len)))) ; for :RETURNS

  :verify-guards nil ; done below
  ///
  (verify-guards atj-gen-deep-term
    :hints (("Goal" :in-theory (enable pseudo-termfnp acl2::pseudo-lambdap)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-deep-fndef-method-name ((fn symbolp))
  :returns (method-name stringp)
  :short "Name of the Java method that builds
          a deeply embedded ACL2 function definition."
  :long
  (xdoc::topstring-p
   "We generate a private static method
    for each deeply embedded ACL2 function definition to build.
    This function generates the name of this method,
    which should be distinct from all the other methods
    generated for the same class.")
  (str::cat
   "$addFunctionDef_"
   (implode (atj-chars-to-jchars-id (explode
                                     (symbol-package-name fn)) nil nil))
   "$$$"
   (implode (atj-chars-to-jchars-id (explode (symbol-name fn)) nil t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-deep-fndef-method ((fn symbolp)
                                   (guards$ booleanp)
                                   (verbose$ booleanp)
                                   (wrld plist-worldp))
  :returns (method jmethodp)
  :verify-guards nil
  :short "Generate a Java method that builds
          a deeply embedded ACL2 function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a private static method
     that contains a sequence of statements to
     store the function's name into a local variable,
     store an array of the function's formal arguments into a local variable,
     store the function's body into a local variable,
     and use these local variables to add the function's definition.")
   (xdoc::p
    "If the @(':guards') input is @('t'),
     we remove all the @(':logic') parts of @(tsee mbe)s;
     if the @(':guards') input is @('nil'),
     we remove all the @(':exec') parts of @(tsee mbe)s.
     We also remove all the non-last arguments
     of @(tsee prog2$)s and @(tsee progn$)s.
     This should remove any occurrences of @(tsee return-last).
     See " (xdoc::seetopic "atj-input-processing" "this discussion")
     " for background.")
   (xdoc::p
    "The indices of the local variables
     to build values, terms, and lambda expressions
     are all reset to 1,
     because each function definition is built in its own method
     (thus, there are no cross-references)."))
  (b* (((run-when verbose$)
        (cw "  ~s0~%" fn))
       (method-name (atj-gen-deep-fndef-method-name fn))
       (jvar-function "function")
       (jvar-formals "formals")
       (jvar-body "body")
       (formals (formals fn wrld))
       (body (ubody fn wrld))
       (in-types (repeat (len formals) :value)) ; actually irrelevant
       (out-type :value) ; actually irrelevant
       ((mv formals body)
        (atj-pre-translate fn formals body in-types out-type t guards$ wrld))
       (fn-block (jblock-locvar *aij-type-named-fn*
                                jvar-function
                                (jexpr-smethod *aij-type-named-fn*
                                               "make"
                                               (list (atj-gen-symbol fn)))))
       (formals-block (jblock-locvar (jtype-array *aij-type-symbol*)
                                     jvar-formals
                                     (atj-gen-deep-formals formals)))
       ((mv body-block
            body-expr
            & & &) (atj-gen-deep-term
                    body "value" 1 "term" 1 "lambda" 1 guards$))
       (body-block (append body-block
                           (jblock-locvar *aij-type-term*
                                          jvar-body
                                          body-expr)))
       (def-block (jblock-imethod (jexpr-name jvar-function)
                                  "define"
                                  (list (jexpr-name jvar-formals)
                                        (jexpr-name jvar-body))))
       (method-body (append fn-block
                            formals-block
                            body-block
                            def-block)))
    (make-jmethod :access (jaccess-private)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-void)
                  :name method-name
                  :params nil
                  :throws nil
                  :body method-body)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-deep-fndef-methods ((fns symbol-listp)
                                    (guards$ booleanp)
                                    (verbose$ booleanp)
                                    (wrld plist-worldp))
  :returns (methods jmethod-listp)
  :verify-guards nil
  :short "Lift @(tsee atj-gen-deep-fndef-method) to lists."
  (if (endp fns)
      nil
    (b* ((first-method
          (atj-gen-deep-fndef-method (car fns) guards$ verbose$ wrld))
         (rest-methods
          (atj-gen-deep-fndef-methods (cdr fns) guards$ verbose$ wrld)))
      (cons first-method rest-methods))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-deep-fndefs ((fns-to-translate symbol-listp))
  :returns (block jblockp)
  :short "Generate Java code to build
          the deeply embedded ACL2 function definitions."
  :long
  (xdoc::topstring-p
   "This is a sequence of calls to the methods
    generated by @(tsee atj-gen-deep-fndef-methods).
    These calls are part of the code that
    initializes (the Java representation of) the ACL2 environment.")
  (if (endp fns-to-translate)
      nil
    (b* ((method-name (atj-gen-deep-fndef-method-name (car fns-to-translate)))
         (first-block (jblock-method method-name nil))
         (rest-block (atj-gen-deep-fndefs (cdr fns-to-translate))))
      (append first-block rest-block))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-deep-call-method ()
  :returns (method jmethodp)
  :short "Generate the Java method to call ACL2 functions,
          in the deep embedding approach."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a public static method,
     which provides the means for external Java code to call
     the deeply embedded Java representations of ACL2 functions."))
  (b* ((method-param-function (make-jparam :final? nil
                                           :type *aij-type-symbol*
                                           :name "function"))
       (method-param-arguments (make-jparam :final? nil
                                            :type (jtype-array
                                                   *aij-type-value*)
                                            :name "arguments"))
       (method-params (list method-param-function
                            method-param-arguments))
       (exception-message "The ACL2 environment is not initialized.")
       (exception-message-expr (atj-gen-jstring exception-message))
       (throw-block (jblock-throw (jexpr-newclass
                                   (jtype-class "IllegalStateException")
                                   (list exception-message-expr))))
       (if-block (jblock-if (jexpr-unary (junop-logcompl)
                                         (jexpr-name "initialized"))
                            throw-block))
       (function-expr (jexpr-smethod *aij-type-named-fn*
                                     "make"
                                     (list (jexpr-name "function"))))
       (call-expr (jexpr-imethod function-expr
                                 "call"
                                 (list (jexpr-name "arguments"))))
       (return-block (jblock-return call-expr))
       (method-body (append if-block
                            return-block)))
    (make-jmethod :access (jaccess-public)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-type *aij-type-value*)
                  :name "call"
                  :params method-params
                  :throws (list *aij-class-eval-exc*)
                  :body method-body)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-deep-init-method ((pkgs string-listp)
                                  (fns-to-translate symbol-listp))
  :returns (method jmethodp)
  :short "Generate the Java public method to initialize the ACL2 environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a public static method,
     which must be called before calling the method to call ACL2 functions,
     and also before calling the AIJ methods
     to translate between Java and ACL2 values.")
   (xdoc::p
    "If the initialization flag is cleared,
     the initialization is performed and the flag is set.
     Otherwise, an exception is thrown,
     because initialization must occur only once.")
   (xdoc::p
    "If @(':deep') is @('t'),
     @('fns-block?') contains code
     to build the deeply embedded representations of the ACL2 functions and
     to validate the definitions of all the deeply embedded ACL2 functions.
     If @(':deep') is @('nil'), @('fns-block?') is @('nil').
     The presence or absence of code in this block
     is the only difference between deep and shallow embedding
     in the initialization method generated here."))
  (b* ((exception-message "The ACL2 environment is already initialized.")
       (exception-message-expr (atj-gen-jstring exception-message))
       (throw-block (jblock-throw (jexpr-newclass
                                   (jtype-class "IllegalStateException")
                                   (list exception-message-expr))))
       (if-block (jblock-if (jexpr-name "initialized")
                            throw-block))
       (pkgs-block (atj-gen-pkgs pkgs))
       (fns-build-block (atj-gen-deep-fndefs fns-to-translate))
       (fns-validate-block (jblock-smethod *aij-type-named-fn*
                                           "validateAll"
                                           nil))
       (initialize-block (jblock-asg-name "initialized"
                                          (jexpr-literal-true)))
       (method-body (append if-block
                            pkgs-block
                            fns-build-block
                            fns-validate-block
                            initialize-block)))
    (make-jmethod :access (jaccess-public)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-void)
                  :name "initialize"
                  :params nil
                  :throws nil
                  :body method-body)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-deep-main-class ((pkgs string-listp)
                                 (fns-to-translate symbol-listp)
                                 (guards$ booleanp)
                                 (java-class$ stringp)
                                 (verbose$ booleanp)
                                 (wrld plist-worldp))
  :returns (class jclassp)
  :verify-guards nil
  :short "Generate the main (i.e. non-test) Java class declaration,
          in the deep embedding approach."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a public class that contains all the generated members.
     [JLS:7.6] says that a Java implementation may require
     public classes to be in files with the same names (plus extension).
     The code that we generate satisfies this requirement.")
   (xdoc::p
    "The class contains the initialization field and method,
     the methods to build the ACL2 packages,
     the methods to build the ACL2 functions,
     and the method to call ACL2 code from external code."))
  (b* ((init-field (atj-gen-init-field))
       ((run-when verbose$)
        (cw "~%Generating Java code for the ACL2 packages:~%"))
       (pkg-methods (atj-gen-pkg-methods pkgs verbose$))
       ((run-when verbose$)
        (cw "~%Generating Java code for the ACL2 functions:~%"))
       (fn-methods (atj-gen-deep-fndef-methods
                    fns-to-translate guards$ verbose$ wrld))
       (init-method (atj-gen-deep-init-method pkgs fns-to-translate))
       (call-method (atj-gen-deep-call-method))
       (body-class (append (list (jcbody-element-member
                                  (jcmember-field init-field)))
                           (jmethods-to-jcbody-elements pkg-methods)
                           (jmethods-to-jcbody-elements fn-methods)
                           (list (jcbody-element-member
                                  (jcmember-method init-method)))
                           (list (jcbody-element-member
                                  (jcmember-method call-method))))))
    (make-jclass :access (jaccess-public)
                 :abstract? nil
                 :static? nil
                 :final? nil
                 :strictfp? nil
                 :name java-class$
                 :superclass? nil
                 :superinterfaces nil
                 :body body-class)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-deep-main-cunit ((guards$ booleanp)
                                 (java-package$ maybe-stringp)
                                 (java-class$ maybe-stringp)
                                 (pkgs string-listp)
                                 (fns-to-translate symbol-listp)
                                 (verbose$ booleanp)
                                 (wrld plist-worldp))
  :returns (cunit jcunitp)
  :verify-guards nil
  :short "Generate the main Java compilation unit,
          in the deep embedding approach."
  (b* ((class (atj-gen-deep-main-class
               pkgs fns-to-translate guards$ java-class$ verbose$ wrld)))
    (make-jcunit :package? java-package$
                 :imports (list (jimport nil (str::cat *aij-package* ".*"))
                                (jimport nil "java.math.BigInteger")
                                (jimport nil "java.util.ArrayList")
                                (jimport nil "java.util.List"))
                 :types (list class))))