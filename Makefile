%.tex: %.lagda
	agda -i /usr/share/agda-stdlib/ -i . --latex --latex-dir report/agda-latex/ --allow-unsolved-metas $<
