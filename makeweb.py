import os
import subprocess
import sys
from datetime import datetime


#
# Generate HTML pages and index for all LaTeX notes.
#

def pandoc_cmd(notename):
    # Specify the CSS file relative to the note location.
    css_file = "../../style.css"
    math_engine = "mathjax"
    pdoc_args = [
        f"notes/{notename}/{notename}.tex",
        "--number-sections",
        f"--{math_engine}",
        f"--css {css_file}",
        f"-f latex -t html5 -s -o notes/{notename}/{notename}.html",
        "--bibliography=references.bib",
        "--metadata=link-citations:true",
        "--metadata=reference-section-title:References",
        "--section-divs",
        "--toc",
        "--citeproc"
    ]
    argstr = " ".join(pdoc_args)
    cmd = f"pandoc {argstr}"
    return cmd

def make_note_pages(notes):
    for note in notes:
        print(f"Building note: '{note}'")
        modified_time = os.path.getmtime(f"notes/{note}/{note}.tex")
        ts = int(modified_time)
        mod_str = datetime.utcfromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print("last modified:", mod_str)
        # TODO: Include last modified date in HTML output of note.
        cmd = pandoc_cmd(note)
        print(cmd)
        proc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE)
        out = proc.stdout.read().decode(sys.stdout.encoding)

def make_index_page_html(notes):
    out_html = "<html>\n"
    out_html += "<head>\n"
    out_html += "<link rel='stylesheet' href='style.css' />\n"
    out_html += "<title>My Notes</title>\n"
    out_html += '<link rel="icon" type="image/x-icon" href="favicon.ico">\n'
    out_html += "<head/>\n"
    out_html += "<body style='padding:20px;'>\n"
    out_html += "<h1>Notes</h1>\n"
    for note in notes:
        note_display_name = note.replace("_", " ")
        out_html += f"<div class='note-link'><a href='notes/{note}/{note}.html'>{note_display_name}</a></div>"
        out_html += "\n"
    out_html += "</body>"
    out_html += "</html>"
    return out_html


notes_dir = "notes"
notes = sorted(os.listdir(notes_dir))
# Notes patterns to ignore.
notes = [n for n in notes if ".DS_Store" not in n]
notes = [n for n in notes if "zzz-note-test" not in n]

make_note_pages(notes)
index_page_html = make_index_page_html(notes)
f = open("index.html", 'w')
f.write(index_page_html)
f.close()