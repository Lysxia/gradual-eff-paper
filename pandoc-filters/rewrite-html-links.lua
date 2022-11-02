-- default to main
local filename = "main.html"

function get_identifier(meta)
	-- get filename from metadata
	for k,v in pairs(meta) do 
		if k == "filename" then
			filename = v
		end
	end
end

function replace_links(el)
	-- href="<original>.html" -> href="<filename>.html"
	if el.format=='html' then
		el.text=el.text:gsub("href=\"(%w+).html", "href=\""..filename..".html")
	end
	return el
end

return {{Meta=get_identifier},{RawBlock=replace_links}}