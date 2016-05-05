all: main.pdf

AGDA_INCLUDE = -i . -i ./agda-stdlib/src

SOURCES = \
	Intro.latex \
	MetaAsm.latex \
	BlockEq.latex \
	Asm.latex \
	Linkers.latex

%.tex: %.lagda
	agda $(AGDA_INCLUDE) --latex --latex-dir . --allow-unsolved-metas $<

.PHONY: checkall

checkall:
	agda $(AGDA_INCLUDE) --allow-unsolved-metas Linkers.lagda

%.pdf: %.latex
	xelatex $<

%.md: %.tex
	cp $< $@

%.latex: %.md
	pandoc $^ -o $@

main.latex: $(SOURCES) sigplanconf-template.tex
	pandoc \
		-R \
		--template=sigplanconf-template.tex \
		-o $@ \
		$(SOURCES)
