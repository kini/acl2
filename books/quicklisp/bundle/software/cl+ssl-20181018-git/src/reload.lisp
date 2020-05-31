;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-
;;;
;;; Copyright (C) 2001, 2003  Eric Marsden
;;; Copyright (C) 2005  David Lichteblau
;;; "the conditions and ENSURE-SSL-FUNCALL are by Jochen Schmidt."
;;;
;;; See LICENSE for details.

;;; We do this in an extra file so that it happens
;;;   - after the asd file has been loaded, so that users can
;;;     customize *libssl-pathname* between loading the asd and LOAD-OPing
;;;     the actual sources
;;;   - before ssl.lisp is loaded, which needs the library at compilation
;;;     time on some implemenations
;;;   - but not every time ffi.lisp is re-loaded as would happen if we
;;;     put this directly into ffi.lisp

#+xcvb (module (:depends-on ("package")))

(in-package :cl+ssl)

(cffi:define-foreign-library libcrypto
  (t "@openssl@/lib/libcrypto.so"))

(cffi:define-foreign-library libssl
  (t "@openssl@/lib/libssl.so"))

(cffi:define-foreign-library libeay32)

(unless (member :cl+ssl-foreign-libs-already-loaded
                *features*)
  (cffi:use-foreign-library libcrypto)
  (cffi:use-foreign-library libssl)
  (cffi:use-foreign-library libeay32))
