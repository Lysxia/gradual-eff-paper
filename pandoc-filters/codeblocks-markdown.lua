-- Transform agda markdown code blocks to agda latex code blocks
-- and indented markdown code blocks to latex displays
-- From agda doc: 
-- Code blocks start with ``` or ```agda on its own line, and end with ```, also on its own line
function CodeBlock(elem)
  if elem.classes[1]=='agda' then 
    return pandoc.RawBlock('markdown', '```\n' .. elem.text .. '\n```')
  end
end



