;; Test mutual recursion
;; Used the standard odd/even test
(let
		((odd (lambda (x [Int])
						(if (zero? x)
								#f
								(even (- x 1)))))
		 (even (lambda (x [Int])
						 (if (zero? x)
								 #t
								 (odd (- x 1))))))
	(assert (odd 1))
	(assert (even 2))
	(assert (odd 3))
	(assert (even 4))
	(assert (even 1234242)))
