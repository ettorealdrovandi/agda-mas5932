# This is a GNUmakefile 
# Purpose:
# (1) htmlgen:
#     Build html versions from the .lagda.md files
#     (1.1) Build the .md files from .lagda.md files
#     (1.2) Build the .html files from the .md, .html Agda primitive, .css
#	    (this uses pandoc)  FIXME
# (2) codegen:
#     Strip away the markdown and generate .agda files
# (3) graph:
#     Build a dependency graph


# Structure:
#
# copyright.txt <--
# hott.agda-lib <--
# Everything.agda <-- generated
# ---src <-- .lagda.md files
# |--style <-- css files
# |--_md   <-- markdown output
# |--html  <-- html output
# |--agda  <-- agda files


.SUFFIXES:
.SUFFIXES: .lagda.md .md .agda .html

SRC   := src
HTML  := html
STYLE := style

# literate agda files
agda_lagda_md := $(shell find $(SRC) -name '*.lagda.md')

################################################################################
#

.PHONY: all htmlgen codegen graph
all : htmlgen codegen graph

################################################################################
# Generate HTML

# ancillary html files and the markdown output from agda --html
agda_md_dir := _md

# See "ordered targets" in the info page for the explanation of '|'
$(agda_md_dir)/mdgen: Everything.agda | $(agda_md_dir)
	agda --html --html-dir=$(agda_md_dir) --html-highlight=auto -i$(SRC) Everything.agda
	touch $(agda_md_dir)/mdgen

Everything.agda: $(agda_lagda_md)
	find . -name  '*.lagda.md' | sed -e 's/\.lagda\.md$$//' -e 's|^\./src/|import\ |' | sort > Everything.agda

$(agda_md_dir):
	mkdir -p $(agda_md_dir)

htmlgen: $(agda_md_dir)/mdgen | pandoc.css $(HTML)
	cp $(agda_md_dir)/Agda.css $(HTML)
	for f in $(agda_md_dir)/*.html; do \
		cp $$f $(HTML) ; \
	done

	for f in $(agda_md_dir)/*.md; do \
		pandoc -s -t html5 --css=pandoc.css --css=Agda.css --mathjax -o $$(echo $$f|sed -e 's|$(agda_md_dir)|$(HTML)|' -e 's|\.md$$|\.html|') $$f; \
	done

pandoc.css: | $(HTML)
	cp $(STYLE)/pandoc.css $(HTML)

$(HTML):
	mkdir $(HTML)

################################################################################
# Dependency graph

graph: hott.svg hott.pdf
#	cp hott.svg hott.pdf ../../assets/

hott.svg: hott.dot
	dot -Tsvg $< > $(patsubst %.dot,%.svg,$<)
hott.pdf: hott.dot
	dot -Tpdf $< > $(patsubst %.dot,%.pdf,$<)

hott.dot: Everything.agda
	agda --dependency-graph=$@ -i$(SRC) Everything.agda


################################################################################
# Code generation: clean the markup away, and leave the agda code.
# Place the code in a directory,  otherwise Agda will complain about
# ambiguous modules: you cannot have name.agda and name.lagda.md
# in the same place

# agda files -- literate mardown stripped away
agda_illiterate := agda
agda_agda := $(subst $(SRC),$(agda_illiterate),$(patsubst %.lagda.md,%.agda,$(agda_lagda_md)))

codegen: $(agda_agda)

$(agda_agda): | $(agda_illiterate)

$(agda_illiterate):
	mkdir $(agda_illiterate)

$(agda_illiterate)/%.agda: $(SRC)/%.lagda.md copyright.txt
#	awk '/```agda$$/,/```$$/' $< |sed -e 's/^```.*//' > $@
	sed -e '1 r copyright.txt' -e '/^```agda$$/,/^```$$/!d' -e 's/^```.*//' $< > $@

################################################################################
# Cleaning and tidying targets

.PHONY: clean clean-md-dir clean-html-dir clean-illiterate clean-interface clean-all

clean-md-dir: 
	-rm $(agda_md_dir)/{*.md,*.html,*.css,mdgen}

clean-html-dir:
	-rm $(HTML)/{*.html,*.css}

clean-graph:
	-rm hott.*

clean: clean-md-dir clean-html-dir clean-graph
	-rmdir $(agda_md_dir)
	-rmdir $(HTML)

clean-illiterate:
	-rm $(agda_illiterate)/*.agda $(agda_illiterate)/*.agdai

# this doesn't clear the _build/ interface files
clean-interface:
	-rm *.agdai $(agda_illiterate)/*.agdai

clean-all: clean-md-dir clean-html-dir clean-interface clean-illiterate
	-rmdir $(agda_md_dir)
	-rmdir $(HTML)
	-rmdir $(agda_illiterate)
