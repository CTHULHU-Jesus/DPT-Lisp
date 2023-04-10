
(enum Enum1
			(E1_1 [Str])
			(E1_2 [Int])
			(E1_3 ))

(enum Enum2
			(E2_1 )
			(E2_2 ))




(define str [Str] "723kky")

(assert (match (E1_1 str)
							 ((E1_3) #f )
							 ((E1_2 x) #f)
							 ((E1_1 x) (eq? x str))))

(assert (match ( E2_1 )
							 ((E2_2) #f)
							 ((default) #t)))

