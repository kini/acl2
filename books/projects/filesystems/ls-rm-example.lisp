(in-package "ACL2")

(include-book "test-stuff")

(defun
    rm-list-extra-hypothesis
    (name-list)
  (declare (xargs :guard (string-listp name-list)))
  (b*
      (((when (atom name-list))
        t)
       (fat32-path (path-to-fat32-path
                        (coerce (car name-list) 'list)))
       ((unless (fat32-filename-list-p fat32-path))
        nil))
    (rm-list-extra-hypothesis (cdr name-list))))

(defthm rm-list-correctness-1-lemma-1
  (equal (mv-nth 1 (rm-list fat32-in-memory path-list 1))
         1))

(defthm
  rm-list-correctness-1-lemma-2
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (equal
     (mv-nth 1
             (hifat-find-file
              (mv-nth 0 (lofat-to-hifat fat32-in-memory))
              fat32-path))
     *enoent*)
    (equal (mv-nth 1 (lofat-to-hifat fat32-in-memory))
           0))
   (equal
    (mv-nth
     1
     (hifat-find-file
      (mv-nth
       0
       (lofat-to-hifat
        (mv-nth 0
                (rm-list fat32-in-memory
                         path-list exit-status))))
      fat32-path))
    *enoent*))
  :hints (("goal" :in-theory (e/d nil (hifat-find-file))
           :induct (rm-list fat32-in-memory
                            path-list exit-status))))

(defthm
  rm-list-correctness-1
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (member-equal path path-list)
    (equal (mv-nth 1
                   (rm-list fat32-in-memory
                            path-list exit-status))
           0)
    (rm-list-extra-hypothesis path-list)
    (equal
     (mv-nth '1
             (lofat-to-hifat fat32-in-memory))
     '0)
    (equal
     (mv-nth '1
             (lofat-to-hifat
              (mv-nth '0
                      (rm-list fat32-in-memory
                               path-list exit-status))))
     '0))
   (not
    (equal
     (mv-nth
      1
      (lofat-lstat
       (mv-nth 0
               (rm-list fat32-in-memory
                        path-list exit-status))
       (path-to-fat32-path (explode path))))
     0)))
  :hints
  (("goal"
    :in-theory (e/d (hifat-lstat)
                    ((:rewrite take-of-take-split)
                     (:linear len-of-member))))))

(defthm ls-list-correctness-1-lemma-1
  (implies (not
            (equal
             (mv-nth
              1
              (ls-list fat32-in-memory name-list exit-status))
             exit-status))
           (equal
            (mv-nth
             1
             (ls-list fat32-in-memory name-list exit-status))
            2))
  :rule-classes :linear)

;; Not currently used.
(defthmd ls-list-correctness-1-lemma-2
  (implies
   (not (equal (mv-nth 1
                       (lofat-lstat fat32-in-memory path))
               0))
   (equal (mv-nth 1
                  (lofat-lstat fat32-in-memory path))
          -1))
  :hints (("goal" :in-theory (enable lofat-lstat))))

(defthm
  ls-list-correctness-1
  (implies
   (and
    (member-equal path name-list)
    (not
     (equal
      (mv-nth 1
              (ls-list fat32-in-memory name-list exit-status))
      2)))
   (and
    (fat32-filename-list-p
     (path-to-fat32-path (explode path)))
    (equal
     (mv-nth
      1
      (lofat-lstat
       fat32-in-memory
       (path-to-fat32-path (explode path))))
     0))))

(defthm lstat-after-unlink-1
  (implies (and (lofat-fs-p fat32-in-memory)
                (fat32-filename-list-p path)
                (equal (mv-nth 1 (lofat-to-hifat fat32-in-memory))
                       0))
           (b* (((mv fat32-in-memory unlink-errno)
                 (lofat-unlink fat32-in-memory path))
                ((mv & lstat-errno)
                 (lofat-lstat fat32-in-memory path)))
             (implies (equal unlink-errno 0)
                      (equal lstat-errno -1))))
  :hints (("goal" :do-not-induct t :in-theory (enable hifat-lstat))))

(defthm
  ls-1-after-rm-1
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (< 0
       (len (intersection-equal ls-paths rm-paths)))
    (rm-list-extra-hypothesis
     rm-paths)
    (equal
     (mv-nth
      '1
      (lofat-to-hifat
       (mv-nth
        '0
        (rm-list
         (mv-nth
          '0
          (string-to-lofat fat32-in-memory disk-image-string))
         rm-paths '0))))
     '0)
    (equal
     (mv-nth
      1
      (lofat-to-hifat
       (mv-nth 0
               (string-to-lofat fat32-in-memory disk-image-string))))
     0))
   (b* (((mv fat32-in-memory
             disk-image-string rm-exit-status)
         (rm-1 fat32-in-memory
               disk-image-string rm-paths))
        ((mv & & ls-exit-status)
         (ls-1 fat32-in-memory
               ls-paths disk-image-string)))
     (implies (equal rm-exit-status 0)
              (equal ls-exit-status 2))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (rm-1 ls-1)
                    ((:rewrite rm-list-correctness-1)
                     ls-list-correctness-1 nth
                     (:definition rm-list)))
    :use
    ((:instance
      (:rewrite rm-list-correctness-1)
      (path
       (nth 0
            (intersection-equal ls-paths rm-paths)))
      (exit-status 0)
      (path-list rm-paths)
      (fat32-in-memory
       (mv-nth
        0
        (string-to-lofat fat32-in-memory disk-image-string))))
     (:instance
      (:rewrite ls-list-correctness-1)
      (exit-status 0)
      (path
       (nth 0
            (intersection-equal ls-paths rm-paths)))
      (name-list ls-paths)
      (fat32-in-memory
       (mv-nth
        0
        (rm-list
         (mv-nth
          0
          (string-to-lofat fat32-in-memory disk-image-string))
         rm-paths 0))))))))
