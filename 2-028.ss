#lang eopl

(require "racket-lib.ss")

(define-datatype lc-exp lc-exp?
  (var-exp
   (var identifier?))
  (lambda-exp
   (bound-var identifier?)
   (body lc-exp?))
  (app-exp
   (left lc-exp?)
   (right lc-exp?)))

(define (unparse-lc-exp exp)
  (cases lc-exp exp
    [var-exp (var)
      (string-append "var-exp("
                     (symbol->string var)
                     ")")]
    [lambda-exp (bound-var body)
      (string-append "lambda-exp( "
                     (symbol->string bound-var)
                     " "
                     (unparse-lc-exp body) " )")]
    [app-exp (left right)
      (string-append "app-exp( "
                     (unparse-lc-exp left)
                     " "
                     (unparse-lc-exp right)
                     " )")]))