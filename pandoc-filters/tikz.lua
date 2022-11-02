local system = require ('pandoc.system')

local tikz_doc_template = [[
\documentclass{standalone}

\usepackage[dvipsnames]{xcolor}
\usepackage{tikz-cd}

\newcommand{\blue}[1]{{\color{blue}#1}}
\newcommand{\red}[1]{{\color{red}#1}}
\newcommand{\RubineRed}[1]{{\color{RubineRed}#1}}
\newcommand{\WildStrawberry}[1]{{\color{WildStrawberry}#1}}

\tikzcdset{every label/.append style = {font = \normalsize}}

\usepackage{fontspec}
\setmonofont[Scale=0.9]{DejaVu mononoki Symbola Droid}
\setmainfont{DejaVu Sans}
\setromanfont{DejaVu Serif}

\begin{document}
\nopagecolor
%s
\end{document}
]]

local function tikz2image(src, filetype, outfile)
  system.with_temporary_directory('tikz2image', function (tmpdir)
    system.with_working_directory(tmpdir, function()
      local f = io.open('tikz.tex', 'w')
      f:write(tikz_doc_template:format(src))
      f:close()
      os.execute('lualatex tikz.tex')
      if filetype == 'pdf' then
        os.rename('tikz.pdf', outfile)
      else
        os.execute('pdf2svg tikz.pdf ' .. outfile)
      end
    end)
  end)
end

extension_for = {
  html = 'svg',
  html4 = 'svg',
  html5 = 'svg',
  latex = 'pdf',
  beamer = 'pdf' }

local function file_exists(name)
  local f = io.open(name, 'r')
  if f ~= nil then
    io.close(f)
    return true
  else
    return false
  end
end

local function starts_with(start, str)
  return str:sub(1, #start) == start
end


function RawBlock(el)
  local path = 'tikz-diagrams/'
  os.execute( "mkdir -p html/tikz-diagrams")
  if starts_with('\\begin{tikzcd}', el.text) then
    local filetype = extension_for[FORMAT] or 'svg'
    local relative_fname = pandoc.sha1(el.text) .. '.' .. filetype
    local fname = system.get_working_directory() .. '/html/'.. path.. relative_fname
    if not file_exists(fname) then
      print("creating files")
      tikz2image(el.text, filetype, fname)
    end
    -- TODO: relative path change?
    return pandoc.Para({pandoc.Image({}, path .. relative_fname)})
  else
   return el
  end
end