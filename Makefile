# To use the makefile, specify the path to source files under SRC
# and the path to pandoc-filters under FILTERS

.PHONY: default all pdf html clean clean_latex clean_html

# path for lagda markdown source file
SRC := src
# path for lua-filters
FILTERS := pandoc-filters
# filename of the final output file
FILENAME := main

AGDA:=agda
build_latex:=_build/latex
src_lagda_tex:=$(build_latex)/src_lagda_tex
src_tex:=$(build_latex)/src_tex
lagda_md_files := $(shell find $(SRC) -name '*.lagda.md')
transpiled_files := $(patsubst $(SRC)/%.md,$(src_lagda_tex)/%.tex,$(lagda_md_files))
latex_files := $(patsubst $(SRC)/%.lagda.md,$(src_tex)/%.tex,$(lagda_md_files)) 
html_files := $(patsubst $(SRC)/%.lagda.md,html/%.html,$(lagda_md_files))
agda_sty := $(src_tex)/agda.sty

EXTRA_DIRS := $(build_latex)/figures

default: pdf

all: pdf draft # html
all_lagda_tex: $(transpiled_files)
all_latex: $(latex_files)

main_pdf := $(build_latex)/$(addsuffix .pdf,$(FILENAME))
draft_pdf := $(build_latex)/draft.pdf

.PHONY : pdf
pdf: all_lagda_tex all_latex main.pdf
draft: all_lagda_tex all_latex draft.pdf

LATEXMK_OPTS := -quiet -outdir=$(build_latex) -auxdir=$(build_latex) -pdf -xelatex

LATEX_DEPS := $(latex_files) $(agda_sty) references.bib $(EXTRA_DIRS)

# A pdf for the whole book
main.pdf: main.tex $(LATEX_DEPS)
	latexmk $(LATEXMK_OPTS) $<
	cp $(main_pdf) main.pdf

draft.pdf: draft.tex main.tex $(LATEX_DEPS)
	latexmk $(LATEXMK_OPTS) $<
	cp $(draft_pdf) draft.pdf

.PHONY : html
html: $(html_files) html/$(addsuffix .html,$(FILENAME)) 
html/$(addsuffix .html,$(FILENAME)) : main.md $(lagda_md_files) $(FILTERS)/include-files.lua template.html
	pandoc --standalone --template=template.html \
	--css ../style.css \
	--lua-filter=$(FILTERS)/include-files.lua $< -o $@
	$(RM) $(html_files)


# General Rules

# for transpiling to new md for html
# pandoc -> agda -> pandoc
# highlight the code only

html/%.html : html/%.md
	pandoc $< \
	--metadata filename=$(FILENAME) \
	--lua-filter=$(FILTERS)/rewrite-html-links.lua \
	--citeproc \
	-o $@


html/%.md : markdown/%.lagda.md
	@echo "Typechecking with Agda"
	@mkdir -p '$(@D)'
	$(AGDA) --html-dir=html \
	--include-path=markdown \
	--html-highlight=code \
	--html $<


markdown/%.lagda.md : $(SRC)/%.lagda.md \
	$(FILTERS)/codeblocks-markdown.lua $(FILTERS)/tikz.lua  $(FILTERS)/citations-tex.lua
	@echo "Inserting Image $<"
	@mkdir -p '$(@D)'
	pandoc  -s  $< \
	--lua-filter=$(FILTERS)/codeblocks-markdown.lua \
	--lua-filter=$(FILTERS)/tikz.lua \
	--lua-filter=$(FILTERS)/citations-tex.lua \
	-o $@

# from https://stackoverflow.com/questions/48267813/makefile-compile-objects-to-different-directory-and-build-from-there
# make a different directory for lagda.tex
$(src_lagda_tex)/%.lagda.tex : $(SRC)/%.lagda.md $(FILTERS)/codeblocks.lua
	@echo "Transpiling $< into $@"
	@mkdir -p '$(@D)'
	pandoc $< --indented-code-classes=default \
		--lua-filter=$(FILTERS)/codeblocks.lua \
		--filter=pandoc-latex-environment \
		-o $@
	sed -i 's/{verbatim}/{Verbatim}/' $@
	sed -i 's/^\\textbackslash /\\/' $@

AGDA_LATEX_OPTS:=--latex --latex-dir=$(src_tex) --include-path=$(src_lagda_tex) --only-scope-checking

# run agda under same directory with lagda.tex	
$(src_tex)/%.tex : $(src_lagda_tex)/%.lagda.tex 
	$(AGDA) $(AGDA_LATEX_OPTS) $<

$(build_latex)/figures:
	ln -sfT ../../figures $@

clean:
	$(RM) -rf _build main.pdf
