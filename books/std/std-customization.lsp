; ACL2 Customization File for The Standard Approach to Using ACL2
; Copyright (C) 2009-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>
; Contributing authors: David Rager <ragerdl@defthm.com>
;                       Keshav Kini <keshav.kini@gmail.com>



; The easiest way to use this file is to just add an acl2-customization.lsp
; file to your home directory that says:
;
;   (ld "std/std-customization.lsp" :dir :system)
;
; You can, of course, put whatever additional customization you want in your
; own customization file, then.


; There's no in-package here, because it could screw up packages loaded by
; custom acl2-customization.lsp files.  Instead we use the #!ACL2 syntax to try
; to make sure this file can be read from any package.

; This file is mentioned in books/doc/practices.lisp.

#!ACL2
(set-deferred-ttag-notes t state)

#!ACL2
(set-inhibit-output-lst '(proof-tree))

;; (f-put-global ':suppress-preload-xdoc t state)

;; (ld "std/std-customization.lsp" :dir :system)

;; (assign verbose-theory-warning nil)
;; (set-inhibit-warnings "non-rec")

;; (set-ld-pre-eval-print nil state)

;; (set-deferred-ttag-notes t state)

;; #!ACL2
;; (defmacro pgv ()
;;   "Taken from :doc print-gv"
;;   '(print-gv :evisc-tuple (evisc-tuple 10 10 nil nil)))

;; #!ACL2
;; (defmacro plev-me ()
;;   `(plev :level 10))

;; #!ACL2
;; (defun monitor-many-fn (rules action state)
;;   (declare (xargs :stobjs (state) :mode :program))
;;   (cond
;;    ((null rules) (value nil))
;;    ((atom rules) (monitor-many-fn (list rules) action state))
;;    (t (er-let* ((val (monitor (car rules) action)))
;;         (monitor-many-fn (cdr rules) action state)))))

;; #!ACL2
;; (defmacro monitor-many (rules &key (action 't))
;;   (let ((action (case action
;;                   (:why '''(:eval :go t))
;;                   (:why-explain '''(:eval :ok-if (brr@ :wonp) (explain)))
;;                   (otherwise action))))
;;     `(let* ((real-rules (expand-ruleset ,rules (w state))))
;;        (er-progn
;;         (brr t)
;;         (monitor-many-fn real-rules ,action state)))))

;; #!ACL2
;; (defmacro where (rule)
;;   ;; Like `why' but stops and lets you inspect the first application
;;   ;; attempt
;;   `(er-progn
;;     (brr t)
;;     (monitor ',rule ''(:eval))))

;; #!ACL2
;; (progn
;;   (defn tree-count (x)
;;     (if (atom x)
;;         1
;;       (+ 1
;;          (tree-count (car x))
;;          (tree-count (cdr x)))))
;;   (memoize 'tree-count))

;; #!ACL2
;; (defmacro ldt (file form &rest rest)
;;   ;; I can never remember the keyword :ld-pre-eval-filter
;;   `(ld ,file :ld-pre-eval-filter ',form ,@rest))

;; (set-inhibit-warnings "skip-proofs" "double-rewrite" "ttag" "non-rec")

;; ;; (include-book "centaur/misc/memory-mgmt" :dir :system)
;; (include-book "tools/plev" :dir :system)
;; (include-book "misc/find-lemmas" :dir :system)

;; (include-book "kestrel/utilities/ubi" :dir :system)
;; (plev-me)

;; (reset-prehistory)

#!ACL2
(with-output
  :off (summary event)
  (progn
    (defun unquote* (x)
      ;; Remove quotes from x until it is no longer quotep.  This is handy for
      ;; utilities that could be called either normally or as keyword commands;
      ;; by unquote*-ing the argument, the tool can accommodate :foo bar, (foo
      ;; bar), :foo 'bar, and (foo 'bar) equally well.
      (if (quotep x)
          (unquote* (unquote x))
        x))

    (defmacro d (arg)
      ;; A handy macro that lets you write :d fn to disassemble a function.  I
      ;; mostly have this because my fingers always type ":diassemble$" instead of
      ;; ":disassemble$"
      (let ((name (unquote* arg)))
        (if (symbolp name)
            `(disassemble$ ',name :recompile nil)
          (er hard? 'd "Not a symbol or quoted symbol: ~x0~%" arg))))

; :why 'x = (why ''x)
; :why '(:k x) = (why ''(:k x))
; :why x = (why 'x)
; :why (:k x) = (why '(:k x))
; (why x)
; (why (:k x))

;

    (defun unquote*-members (x)
      (and (consp x)
           (cons-with-hint (unquote* (car x))
                           (unquote*-members (cdr x))
                           x)))

    (defun monitor-many-fn1 (rules action state)
      (declare (xargs :stobjs (state) :mode :program))
      ((let* ((wrld (w state)))
         (if (null rules)
             (value nil)
           (er-let* ((val (monitor (car rules) action)))
             (monitor-many-fn1 (cdr rules) action state))))))

    (defun monitor-many-fn (rules action state)
      (declare (xargs :stobjs (state) :mode :program))
      (let ((action (case action
                      (:why '''(:eval :go t))
                      (:why-explain '''(:eval :ok-if (brr@ :wonp)
                                              (explain)))
                      (otherwise action)))
            (rules (unquote*)))
        (er-progn
         (with-output! :off :all
           (monitor-many-fn1 rules action state))
         (brr t))))

    (defmacro monitor-many (rules &key (action 't))
      `(monitor-many-fn ,rules ,action state)
      (let ()
        `(er-progn
          (with-output! :off :all
            (monitor-many-fn ,rules ,action state))
          (brr t))))

    (defmacro why (rule &rest rules)
      (monitor-many))

    (defmacro why (rule)
      ;; A handy macro that lets you figure out why a rule isn't firing.
      ;; This is useful to me because I can never remember the :monitor
      ;; syntax.
      `(er-progn
        (brr t)
        (monitor ',(or (and (consp rule)
                            (equal (car rule) 'quote)
                            (cadr rule))
                       rule)
                 ''(:eval :go t))))

    (defun explain-fn (state)
      (declare (xargs :stobjs (state)
                      :mode :program))
      (mv-let (clause ttree)
        (clausify-type-alist (get-brr-local 'type-alist state)
                             (list (cddr (get-brr-local 'failure-reason state)))
                             (ens state) (w state) nil nil)
        (declare (ignore ttree))
        (prettyify-clause clause
                          nil
                          (w state))))

    (defmacro explain ()
      `(prog2$ (cw "Printing target with hyps derived from type-alist~%")
               (explain-fn state)))

    (defmacro why-explain (rule)
      `(er-progn
        (brr t)
        (monitor ',rule ''(:eval
                           :ok-if (brr@ :wonp)
                           (explain)))))

    (defmacro with-redef (&rest forms)
      ;; A handy macro you can use to temporarily enable redefinition, but then
      ;; keep it disabled for the rest of the session
      `(progn
         (defttag with-redef)
         (progn!
          (set-ld-redefinition-action '(:doit . :overwrite) state)
          (progn . ,forms)
          (set-ld-redefinition-action nil state))))))



; XDOC SUPPORT
;
;   - Always load the xdoc package, which is pretty fast.
;
;   - Unless :SUPPRESS-PRELOAD-XDOC has been assigned, also get the xdoc
;     database preloaded so that :XDOC commands are very fast and never
;     leave any nonsense in your history.
;
; The second part is somewhat slow and makes ACL2 take noticeably longer to
; boot up.  However, for me, on the par, it seems worth it to make :xdoc much
; more useful.
;
; The suppress-preload-xdoc mechanism can be used to make sure that xdoc does
; NOT get preloaded.  Why would you want to do this?
;
; Well, a few libraries (e.g., str) have some files (package definitions,
; str::cat, etc.) that are included in the xdoc implementation code that gets
; loaded by (xdoc::colon-xdoc-init).  When you're hacking on these libraries,
; it's very easy to, e.g., change something that causes xdoc to be completely
; unloadable until you recertify everything.
;
; At any rate, if for this (or some other reason) you don't want to
; automatically do this xdoc initialization, you can just add:
;
;   (assign :suppress-preload-xdoc t)
;
; Before loading std-customization.lsp.

#!ACL2
(with-output
  :off (summary event)
  (ld "std/package.lsp" :dir :system))

#!ACL2
(make-event
 (if (not (boundp-global :suppress-preload-xdoc state))
     `(progn
        (include-book "xdoc/top" :dir :system)
        (include-book "xdoc/debug" :dir :system)
        (xdoc::colon-xdoc-init))
   `(value-triple nil)))


; maybe actually report correct times
(assign get-internal-time-as-realtime t)
