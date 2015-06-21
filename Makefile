%.tex: %.lagda
	agda -i ./agda-stdlib/src -i . --latex --latex-dir report/agda-latex/ --allow-unsolved-metas $<
