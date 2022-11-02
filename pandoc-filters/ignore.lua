function RawBlock(elem)
	if elem.format ~= FORMAT then
		return pandoc.Null()
	end
end

function RawInline(elem)
	if elem.format ~= FORMAT then
		return pandoc.Null()
	end
end