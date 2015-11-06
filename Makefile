AGDA_INCLUDE = -i . -i ./agda-stdlib/src

%.tex: %.lagda
	agda $(AGDA_INCLUDE) --latex --latex-dir . --allow-unsolved-metas $<

.PHONY: checkall

checkall:
	agda $(AGDA_INCLUDE) Functions.lagda
