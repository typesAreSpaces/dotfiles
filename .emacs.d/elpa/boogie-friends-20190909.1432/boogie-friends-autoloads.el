;;; boogie-friends-autoloads.el --- automatically extracted autoloads
;;
;;; Code:
(add-to-list 'load-path (directory-file-name (or (file-name-directory #$) (car load-path))))

;;;### (autoloads nil "boogie-mode" "boogie-mode.el" (24009 3675
;;;;;;  355492 476000))
;;; Generated autoloads from boogie-mode.el

(add-to-list 'auto-mode-alist '("\\.bpl\\'" . boogie-mode))

(autoload 'boogie-mode "boogie-mode" "\
Major mode for editing Boogie programs.

\\{boogie-mode-map}

\(fn)" t nil)

;;;***

;;;### (autoloads nil "dafny-mode" "dafny-mode.el" (24009 3675 315492
;;;;;;  509000))
;;; Generated autoloads from dafny-mode.el

(autoload 'dafny-test-suite-open-diff "dafny-mode" "\


\(fn DFY-NAME)" t nil)

(autoload 'dafny-test-suite-accept-diff "dafny-mode" "\


\(fn DFY-NAME)" t nil)

(add-to-list 'auto-mode-alist '("\\.dfy\\'" . dafny-mode))

(autoload 'dafny-mode "dafny-mode" "\
Major mode for editing Dafny programs.

\\{dafny-mode-map}

\(fn)" t nil)

;;;***

;;;### (autoloads nil "z3-smt2-mode" "z3-smt2-mode.el" (24009 3675
;;;;;;  467492 384000))
;;; Generated autoloads from z3-smt2-mode.el

(add-to-list 'auto-mode-alist '("\\.smt2\\'" . z3-smt2-mode))

(autoload 'z3-smt2-mode "z3-smt2-mode" "\
Major mode for editing SMT2 programs.

\\{z3-smt2-mode-map}

\(fn)" t nil)

;;;***

;;;### (autoloads nil nil ("boogie-friends-pkg.el" "boogie-friends.el"
;;;;;;  "dafny-docs.el" "inferior-dafny.el") (24009 3675 339492 489000))

;;;***

;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; End:
;;; boogie-friends-autoloads.el ends here
