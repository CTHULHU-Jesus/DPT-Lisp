(enum Option T
			(Some [T])
			(None))
;; This is the function composition operator
(define o (lambda (f1 [-> A B] f2 [-> B C] ) (lambda (x [A]) (f2 (f1 x)))))

