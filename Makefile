all: main.pdf

AGDA_INCLUDE = -i . -i ./agda-stdlib/src

SOURCES = \
	Intro.latex \
	MetaAsm.latex \
	Asm.latex \
	BlockEq.latex \
	Programs.latex \
	Linkers.latex \
	LazyLinkers.latex

%.tex: %.lagda
	rm -f *.agdai && \
	agda $(AGDA_INCLUDE) --latex --latex-dir . --allow-unsolved-metas $<

.PHONY: checkall

checkall:
	agda $(AGDA_INCLUDE) --allow-unsolved-metas Linkers.lagda

%.pdf: %.latex
	xelatex $<

%.md: %.tex
	cp $< $@

%.latex: %.md
	pandoc \
		--listings \
		$^ -o $@

main.latex: $(SOURCES) sigplanconf-template.tex
	pandoc \
		-R \
		--template=sigplanconf-template.tex \
		-o $@ \
		$(SOURCES)
