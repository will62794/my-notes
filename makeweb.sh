#!/bin/sh
for d in `ls -d */`; do
    pandoc $d/$d.tex --css pandoc.css -f latex -t html5 -s -o $d/$d.html
done