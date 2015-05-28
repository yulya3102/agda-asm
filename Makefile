AGDA = DevCore SSA NotSSA Meta Functions

agda:
	@for lagda in $(AGDA) ; do \
		agda -i /usr/share/agda-stdlib/ -i . --latex --latex-dir report/agda-latex/ --allow-unsolved-metas $$lagda.lagda; \
		mv report/agda-latex/$$lagda.tex report/agda-latex/$$lagda.latex; \
	done
