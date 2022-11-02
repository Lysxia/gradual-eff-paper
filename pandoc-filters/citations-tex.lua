-- read latex citation block and transform to Pandoc Cite blocks

function RawInline(el)
	local isShort = false
	if el.format == "tex"  and el.text:match("cite") then
		-- remember if the citation is short
		if el.text:match("^\\(%w+)cite{") == "short" then
			isShort = true
		end
		-- transform shortcite to cite for parsing
		el.text = el.text:gsub("^\\(%w+)cite{(%g+)}$", "\\cite{%2}")
		-- from documentation for pandoc.read
		local doc = pandoc.read(el.text,"latex")
		local block = doc.blocks[1]
		assert(block.content[1].t == "Cite")
		-- change to SuppressAuthor if shortcite 
		if isShort then
			for i, citation in ipairs(block.content[1].c[1]) do
				citation.mode = "SuppressAuthor"
			end
		end
		return block.content[1]
	end
end