for i in *.thy
do
	awk -f text.awk $i > new/$i
done
