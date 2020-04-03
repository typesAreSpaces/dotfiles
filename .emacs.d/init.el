;; load emacs 24's package system. Add MELPA repository.

;; Added by Package.el.  This must come before configurations of
;; installed packages.  Don't delete this line.  If you don't want it,
;; just comment it out by adding a semicolon to the start of the line.
;; You may delete these explanatory comments.
(package-initialize)

(when (>= emacs-major-version 24)
  (require 'package)
  (add-to-list
   'package-archives
   ;; '("melpa" . "http://stable.melpa.org/packages/") ; many packages won't show if using stable
   '("melpa" . "http://melpa.milkbox.net/packages/")
   t))

(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(custom-safe-themes
   (quote
    ("274fa62b00d732d093fc3f120aca1b31a6bb484492f31081c1814a858e25c72e" default)))
 '(package-selected-packages
   (quote
    (2048-game 4clojure evil bison-mode boogie-friends org-edna bar-cursor dante auctex iedit auto-complete-c-headers auto-complete company-irony company-irony-c-headers flycheck-irony dracula-theme rust-mode fstar-mode tide))))
(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 )

;; Open .v files with Proof General's Coq mode
;(load "~/.emacs.d/lisp/PG/generic/proof-site")
;; Let Proof General find coqtop
;(setq coq-prog-name "/home/jose/.opam/system/bin/coqtop") 

(load-theme 'dracula)
(show-paren-mode t)

;; Start auto-complete with emacs
(require 'auto-complete)
;; Do default config for auto-complete
(require 'auto-complete-config)
(ac-config-default)
;; ;; Start yasnippet with emacs
;; (require 'yasnippet)
;; (yas-global-mode t)
;; (define-key yas-minor-mode-map (kbd "<M-tab>") 'yas-expand)

;; Macro which initializes auto-complete-c-headers and gets called for c/c++ hooks
(defun my:ac-c-header-init ()
  (require 'auto-complete-c-headers)
  (add-to-list 'ac-sources  'ac-source-c-headers)
  (add-to-list 'achead:include-directories '"/usr/include/c++/7") 
  (add-to-list 'achead:include-directories '"/usr/include")
  )
(add-hook 'c++-mode-hook 'my:ac-c-header-init)
(add-hook 'c-mode-hook 'my:ac-c-header-init)

;; Fix iedit bug
(define-key global-map (kbd "C-c ;") 'iedit-mode)

;; Turn on Semantic
(semantic-mode t)
(defun my:add-semantic-to-autocomplete()
  (add-to-list 'ac-sources 'ac-source-semantic)
  )
(add-hook 'c-mode-common-hook 'my:add-semantic-to-autocomplete)

;; Turn on ede-mode
(global-ede-mode t)
(ede-cpp-root-project "masterThesis"
		      :file "/home/jose/Documents/GithubProjects/master-thesis/Software/Cpp/EUFInterpolantsZ3/src/main.cpp" 
		      :include-path '("/../include")
		      )
;; Turn on automatic reparsing of open buffers in semantic
(global-semantic-idle-scheduler-mode t)

;; (add-hook 'c++-mode-hook 'irony-mode)
;; (add-hook 'c-mode-hook 'irony-mode)
;; (add-hook 'objc-mode-hook 'irony-mode)

;; (defun my-irony-mode-hook ()
;;   (define-key irony-mode-map
;;       [remap completion-at-point] 'counsel-irony)
;;   (define-key irony-mode-map
;;       [remap complete-symbol] 'counsel-irony))
;; (add-hook 'irony-mode-hook 'my-irony-mode-hook)
;; (add-hook 'irony-mode-hook 'irony-cdb-autosetup-compile-options)

;; Latex IDE
(setq TeX-auto-save t)
(setq TeX-parse-self t)
(setq TeX-save-query nil)

(require 'flymake)

(defun flymake-get-tex-args (file-name)
  (list "pdflatex"
	(list "-file-line-error" "-draftmode" "-interaction=nonstopmode" file-name)))

;; (add-hook 'LaTeX-mode-hook 'flymake-mode)
					; could be ispell as well, depending on your preferences
(setq ispell-program-name "aspell") 
					; this can obviously be set to any language your spell-checking program supports
(setq ispell-dictionary "english") 

(add-hook 'LaTeX-mode-hook 'flyspell-mode)
(add-hook 'LaTeX-mode-hook 'flyspell-buffer)

(defun turn-on-outline-minor-mode ()
  (outline-minor-mode 1))

(add-hook 'LaTeX-mode-hook 'turn-on-outline-minor-mode)
(setq outline-minor-mode-prefix "\C-c \C-o") 

(put 'set-goal-column 'disabled nil)

(define-key global-map "\M-*" 'pop-tag-mark)

(require 'evil)
(evil-mode t)
