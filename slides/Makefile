.PHONY: build serve clean svg

AGDA:=agda
MODULE:=Code
TEMPLATE:=html/$(MODULE).md

TEMPLATE_SCRIPT:=scripts/jinja.py

build: static/index.html static/Agda.css svg

serve:
	sh ./scripts/serve.sh

static/index.html: $(TEMPLATE_SCRIPT) $(TEMPLATE) src/index.html.template
	python3 $(TEMPLATE_SCRIPT)

static/Agda.css: html/Agda.css
	cp $< $@

html/$(MODULE).md html/Agda.css: src/$(MODULE).lagda.md
	$(AGDA) --verbose=0 -i../src -isrc --html --html-highlight=code $<

svg: static/cast-left-plus-tex.svg static/cast-left-minus-tex.svg

static/%-tex.svg: src/%.tex
	latexmk -auxdir=build -outdir=build -shell-escape -pdf $<
	pdf2svg build/$(*F).pdf $@

clean:
	$(RM) -r html build
