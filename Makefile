test:
	cargo insta test --test bool
	cargo insta test --test ecta_conversion
	cargo insta test --test sketch_order
	cargo insta test --test nat
	cargo insta test --test list

review:
	cargo insta review

dot:
	dot -Tpng test.dot > outfile.png