(define is-odd
  (letrec (
    (is-odd [-> Int Bool]
      (lambda (x [INT])
        (if (eq? x 0)
        false
        (is-even (- x 1)))))
    (is-even [-> Int Bool]
      (lambda (x [Int])
        if (eq? x 0)
        true
        (is-odd (- x 1))))
 ) is-odd )
)

(assert? (is-odd 1))
(assert? (is-odd 3))
(assert? (is-odd 1001))
