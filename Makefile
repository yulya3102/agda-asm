%.tex: %.lagda
	agda -i ./agda-stdlib/src -i . --latex --latex-dir . --allow-unsolved-metas $<
