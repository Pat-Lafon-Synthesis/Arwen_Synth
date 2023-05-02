test:
	cargo insta test --test bool
	cargo insta test --test nat
	cargo insta test --test list

review:
	cargo insta review