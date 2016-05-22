BUILD=build

all: $(BUILD)/main.pdf

AGDA_INCLUDE = -i . -i ./agda-stdlib/src

SOURCES = \
	$(BUILD)/Intro.latex \
	$(BUILD)/MetaAsm.latex \
	$(BUILD)/Asm.latex \
	$(BUILD)/BlockEq.latex \
	$(BUILD)/Programs.latex \
	$(BUILD)/Linkers.latex \
	$(BUILD)/Conclusion.latex

$(BUILD)/agda.sty: agda.sty
	cp $< $@

$(BUILD)/%.tex: %.lagda $(BUILD)/agda.sty
	rm -f *.agdai && \
	agda $(AGDA_INCLUDE) --latex --latex-dir $(BUILD) --allow-unsolved-metas $<

.PHONY: checkall

checkall:
	agda $(AGDA_INCLUDE) --allow-unsolved-metas Linkers.lagda

$(BUILD)/%.pdf: $(BUILD)/%.latex bib.bib
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

$(BUILD)/main.latex: $(SOURCES) sigplanconf-template.tex $(BUILD)/Abstract.latex
	pandoc \
		-R \
		--template=sigplanconf-template.tex \
		-o $@ \
		$(SOURCES)
