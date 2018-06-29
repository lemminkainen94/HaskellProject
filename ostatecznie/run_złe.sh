#!/bin/bash
for filename in złe/*; do
        echo "$filename"
        echo "---------"
        cat "$filename"
        echo "----------"
        ./Main "$filename"
        echo "==============================="
done

