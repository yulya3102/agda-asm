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

$(BUILD)/%.tex: %.lagda
	rm -f *.agdai && \
	agda $(AGDA_INCLUDE) --latex --latex-dir $(BUILD) --allow-unsolved-metas $<

.PHONY: checkall

checkall:
	agda $(AGDA_INCLUDE) --allow-unsolved-metas Linkers.lagda

$(BUILD)/%.pdf: $(BUILD)/%.latex
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
		$^ -o $@

$(BUILD)/main.latex: $(SOURCES) sigplanconf-template.tex
	pandoc \
		-R \
		--template=sigplanconf-template.tex \
		-o $@ \
		$(SOURCES)
