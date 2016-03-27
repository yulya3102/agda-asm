all: main.pdf

AGDA_INCLUDE = -i . -i ./agda-stdlib/src

SOURCES = \
	Intro.md \
	MetaAsm.md \
	BlockEq.md \
	Asm.md \
	Programs.md

%.tex: %.lagda
	agda $(AGDA_INCLUDE) --latex --latex-dir . --allow-unsolved-metas $<

.PHONY: checkall

checkall:
	agda $(AGDA_INCLUDE) --allow-unsolved-metas Programs.lagda

%.pdf: %.md include.tex
	pandoc -w latex --include-in-header include.tex --latex-engine xelatex $< -o $@

%.md: %.tex
	mv $< $@

main.md: $(SOURCES)
	pandoc $^ -o $@
