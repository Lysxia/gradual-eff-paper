.PHONY: build serve clean

AGDA:=agda
MODULE:=Code
TEMPLATE:=html/$(MODULE).md

TEMPLATE_SCRIPT:=scripts/jinja.py

build: static/index.html static/Agda.css

serve:
	sh ./scripts/serve.sh

static/index.html: $(TEMPLATE_SCRIPT) $(TEMPLATE) src/index.html.template
	python3 $(TEMPLATE_SCRIPT)

static/Agda.css: html/Agda.css
	cp $< $@

html/$(MODULE).md html/Agda.css: src/$(MODULE).lagda.md
	$(AGDA) --verbose=0 -i../src -isrc --html --html-highlight=code $<

clean:
	$(RM) -r html
