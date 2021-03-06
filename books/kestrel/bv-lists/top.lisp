; A library about lists of bit vectors.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-unsigned-byte-p")
(include-book "all-unsigned-byte-p-of-reverse-list")
(include-book "all-unsigned-byte-p-of-repeat")
(include-book "all-all-unsigned-byte-p")
(include-book "unsigned-byte-listp")
(include-book "len-mult-of-8p")
(include-book "bits-to-byte")
(include-book "bits-to-byte-little")
(include-book "bits-to-bytes")
(include-book "bits-to-bytes-little")
(include-book "byte-to-bits")
(include-book "byte-to-bits-little")
(include-book "bytes-to-bits")
(include-book "bytes-to-bits-little")
(include-book "bvxor-list")
(include-book "bvchop-list")

(include-book "width-of-widest-int")

(include-book "packbv-def")
(include-book "packbv")
(include-book "unpackbv")
(include-book "packbv-and-unpackbv")

(include-book "bv-arrayp")
(include-book "bv-array-read")
(include-book "bv-array-write")
