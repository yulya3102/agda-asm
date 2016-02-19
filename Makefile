AGDA_INCLUDE = -i . -i ./agda-stdlib/src

%.tex: %.lagda
	agda $(AGDA_INCLUDE) --latex --latex-dir . --allow-unsolved-metas $<

.PHONY: checkall

checkall:
	agda $(AGDA_INCLUDE) Functions.lagda

%.pdf: %.md include.tex
	pandoc -w latex --include-in-header include.tex --latex-engine xelatex $< -o $@

%.md: %.tex
	mv $< $@
