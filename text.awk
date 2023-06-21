BEGIN {
}
END {
}
/^text \\<open>/ {
	intext = 1;
	print $0;
	next;
}
/^\\<close>/ {
	intext = 0;
	print $0;
	next;
}
(intext == 1) {
	line = $0;
	#gsub(/\\<[^>]*>/,"@{term &}",line);
	gsub(/\\<delta>/,"@{term \\<delta>}",line);
	gsub(/\\<delta>}A/,"\\<delta>A}",line);
	gsub(/\\<epsilon>/,"@{term \\<epsilon>}",line);
	gsub(/\\<epsilon>}A/,"\\<epsilon>A}",line);
	gsub(/\\<Phi>/,"@{term \\<Phi>}",line);
	print line;
}
(intext == 0) {
	print $0;
}
