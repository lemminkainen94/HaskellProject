#!/bin/bash
for filename in dobre/*; do
	echo "$filename"
	echo "---------"
	cat "$filename"
   	echo "----------"
	./Main "$filename"
        echo "==============================="
done
