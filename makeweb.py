import os
import subprocess
import sys

#
# Generate HTML pages and index for all LaTeX notes.
#

def pandoc_cmd(notename):
    # Specify the CSS file relative to the note location.
    css_file = "../../style.css"
    math_engine = "mathjax"
    cmd = f"pandoc notes/{notename}/{notename}.tex --number-sections --{math_engine} --css {css_file} -f latex -t html5 -s -o notes/{notename}/{notename}.html"
    return cmd

def make_note_pages(notes):
    for note in notes:
        cmd = pandoc_cmd(note)
        print(cmd)
        proc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE)
        out = proc.stdout.read().decode(sys.stdout.encoding)

def make_index_page_html(notes):
    out_html = "<html>\n"
    out_html += "<body style='padding:20px;'>"
    out_html += "<link rel='stylesheet' href='style.css' />"
    out_html += "<h1>Notes</h1>\n"
    for note in notes:
        out_html += f"<div><a href='notes/{note}/{note}.html'>{note}</a></div>"
        out_html += "\n"
    out_html += "</body>"
    out_html += "</html>"
    return out_html


notes_dir = "notes"
notes = sorted(os.listdir(notes_dir))
make_note_pages(notes)
index_page_html = make_index_page_html(notes)
f = open("index.html", 'w')
f.write(index_page_html)
f.close()