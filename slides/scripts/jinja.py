from jinja2 import Environment, FileSystemLoader
env = Environment(
    loader = FileSystemLoader(["src/","html/"]),
    variable_start_string="{{*",
    variable_end_string="*}}",
    comment_start_string="{#{",
    comment_end_string="}#}")
template = env.get_template("Code.md")
with open("static/index.html", mode="w", encoding="utf-8") as outfile:
    outfile.write(template.render())
