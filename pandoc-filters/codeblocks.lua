-- Transform agda markdown code blocks to agda latex code blocks
-- and indented markdown code blocks to latex displays
-- From agda doc: 
-- Code blocks start with ``` or ```agda on its own line, and end with ```, also on its own line
function CodeBlock(elem)
  if #(elem.classes)==0 or elem.classes[1]=='agda' then 
    return pandoc.RawBlock('tex', '\\begin{code}\n' .. elem.text .. '\n\\end{code}')
  else 
    return pandoc.RawBlock('tex', '\\begin{verbatim}\n' .. elem.text .. '\n\\end{verbatim}')
  end
end



