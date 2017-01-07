BUILD=build
TEMPLATE = sigplanconf-template.tex

all: $(BUILD)/main.pdf

AGDA_INCLUDE = -i .. -i ../agda-stdlib/src

SOURCES = \
	$(BUILD)/Intro.latex \
	$(BUILD)/Primer.latex \
	$(BUILD)/TAL_difference.latex \
	$(BUILD)/Core.latex \
	$(BUILD)/TAL_types.latex \
	$(BUILD)/MetaAsm.latex \
	$(BUILD)/Asm.latex \
	$(BUILD)/DynLinkLoading.latex \
	$(BUILD)/Linkers.latex \
	$(BUILD)/BlockEqDefinition.latex \
	$(BUILD)/BlockEq.latex \
	$(BUILD)/EquivalenceProof.latex \
	$(BUILD)/Loader.latex \
	$(BUILD)/Conclusion.latex \
	$(BUILD)/Appendix.latex \
	$(BUILD)/BlockEqIsEq.latex \
	$(BUILD)/RuntimeEq.latex \
	$(BUILD)/Acknowledgements.latex

INCLUDE_EXAMPLES = \
	$(BUILD)/eq-blocks-example.asm \
	$(BUILD)/eq-exblocks-example.asm

IMAGES = \
	$(BUILD)/objfile.jpg \
	$(BUILD)/memory.jpg

$(BUILD)/agda.sty: agda.sty
	cp $< $@

$(BUILD)/%.tex: ../%.lagda
	rm -f *.agdai && \
		agda $(AGDA_INCLUDE) --latex --latex-dir $(BUILD) $<
	rm -f $(BUILD)/agda.sty

.PHONY: checkall

checkall:
	agda $(AGDA_INCLUDE) ../Linkers.lagda
	agda $(AGDA_INCLUDE) ../BlockEqIsEq.lagda

$(BUILD)/main.pdf: $(IMAGES)

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

$(BUILD)/%: %
	cp $< $@

$(BUILD)/%.md: $(BUILD)/%.tex
	cp $< $@

$(BUILD)/%.latex: $(BUILD)/%.md
	pandoc \
		--listings \
		--natbib \
		$^ -o $@

$(BUILD)/main.latex: Makefile $(SOURCES) $(TEMPLATE) $(BUILD)/Abstract.latex $(INCLUDE_EXAMPLES)
	pandoc \
		-R \
		--template=$(TEMPLATE) \
		-o $@ \
		$(SOURCES)

objfile.jpg:
	wget -O $@ https://www.dropbox.com/s/f9umac2lo3c9b63/objfile.jpg?dl=0

memory.jpg:
	wget -O $@ https://www.dropbox.com/s/dtgodj9pjm0nm2y/memory.jpg?dl=0
