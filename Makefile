BUILD=build

all: $(BUILD)/main.pdf

AGDA_INCLUDE = -i . -i ./agda-stdlib/src

SOURCES = \
	$(BUILD)/Intro.latex \
	$(BUILD)/MetaAsm.latex \
	$(BUILD)/Asm.latex \
	$(BUILD)/Linkers.latex \
	$(BUILD)/BlockEq.latex \
	$(BUILD)/Loader.latex \
	$(BUILD)/Conclusion.latex \
	$(BUILD)/Appendix.latex \
	$(BUILD)/BlockEqIsEq.latex \
	$(BUILD)/RuntimeEq.latex

INCLUDE_EXAMPLES = \
	eq-blocks-example.asm \
	eq-exblocks-example.asm

$(BUILD)/agda.sty: agda.sty
	cp $< $@

$(BUILD)/%.tex: %.lagda
	rm -f *.agdai && \
	agda $(AGDA_INCLUDE) --latex --latex-dir $(BUILD) --allow-unsolved-metas $<
	rm -f $(BUILD)/agda.sty

.PHONY: checkall

checkall:
	agda $(AGDA_INCLUDE) --allow-unsolved-metas Linkers.lagda

$(BUILD)/%.pdf: $(BUILD)/%.latex bib.bib $(BUILD)/agda.sty
	xelatex \
		-output-directory=$(BUILD) \
		$<
	bibtex $(<:.latex=.aux)
	xelatex \
		-output-directory=$(BUILD) \
		$<
	xelatex \
		-output-directory=$(BUILD) \
		$<

$(BUILD)/%.md: %.md
	cp $< $@

$(BUILD)/%.md: $(BUILD)/%.tex
	cp $< $@

$(BUILD)/%.latex: $(BUILD)/%.md
	pandoc \
		--listings \
		--natbib \
		$^ -o $@

$(BUILD)/main.latex: Makefile $(SOURCES) sigplanconf-template.tex $(BUILD)/Abstract.latex $(INCLUDE_EXAMPLES)
	pandoc \
		-R \
		--template=sigplanconf-template.tex \
		-o $@ \
		$(SOURCES)
