(define (report-error who fmt . args)
  (error who (apply format fmt args)))
