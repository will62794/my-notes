import os
import subprocess
import sys
from datetime import datetime


#
# Generate HTML pages and index for all LaTeX notes.
#

PAPERS_DIR = "notes/Papers"

def pandoc_cmd(notename, subdir="notes"):
    # Specify the CSS file relative to the note location.
    css_file = "/style.css"
    math_engine = "mathjax"
    pdoc_args = [
        f"{subdir}/{notename}/{notename}.tex",
        "--number-sections",
        f"--{math_engine}",
        f"--css {css_file}",
        f"-f latex -t html5 -s -o {subdir}/{notename}/{notename}.html",
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

def make_papers_pages(paper_notes):
    for note in paper_notes:
        print(f"Building note: '{note}'")
        # modified_time = os.path.getmtime(f"notes/{note}/{note}.tex")
        # ts = int(modified_time)
        # mod_str = datetime.utcfromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        # print("last modified:", mod_str)
        # TODO: Include last modified date in HTML output of note.
        cmd = pandoc_cmd(note, subdir=PAPERS_DIR)
        print(cmd)
        proc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE)
        out = proc.stdout.read().decode(sys.stdout.encoding)

def make_index_page_html(notes, title="Notes", papers_page=False, subdir="notes"):
    out_html = "<html>\n"
    out_html += "<head>\n"
    out_html += "<link rel='stylesheet' href='./style.css' />\n"
    out_html += "<link rel='stylesheet' href='../../style.css' />\n"
    out_html += "<link rel='stylesheet' href='../../../style.css' />\n"
    out_html += "<title>My Notes</title>\n"
    out_html += '<link rel="icon" type="image/x-icon" href="favicon.ico">\n'
    out_html += "<head/>\n"
    out_html += "<body style='padding:20px;'>\n"
    out_html += f"<h1>{title}</h1>\n"
    # out_html += "<p><a style='font-size:14px' href='https://github.com/will62794/my-notes'>Github</a></p>\n"
    out_html += "<div style='width:20px;padding-bottom:15px;'><a style='font-size:14px' href='https://github.com/will62794/my-notes'><img src='./github-mark.png' width=15></img></a></div>\n"
    out_html += "<div style='width:20px;padding-bottom:15px;'><a style='font-size:14px' href='index.html'>Home</a></div>\n"
    for note in notes:
        conf_name = ""
        if papers_page:
            conf_name = "".join(note.split("_")[-2:])
        note_display_name = note.replace("_", " ")
        
        out_html += f"<div class='note-link'><a href='{subdir}/{note}/{note}.html'>{note_display_name}</a></div>"
        out_html += "\n"
    # Add papers link.
    if not papers_page:
        note_display_name = "Papers"
        out_html += f"<br><div class='note-link'><a href='papers.html'>{note_display_name}</a></div>"
        out_html += "\n"
    out_html += "</body>"
    out_html += "</html>"
    return out_html


notes_dir = "notes"
notes = sorted(os.listdir(notes_dir))
# Notes patterns to ignore.
notes = [n for n in notes if ".DS_Store" not in n]
notes = [n for n in notes if "zzz-note-test" not in n]
notes = [n for n in notes if "Papers" not in n]

paper_notes = sorted(os.listdir(PAPERS_DIR))


make_note_pages(notes)
make_papers_pages(paper_notes)
index_page_html = make_index_page_html(notes)
f = open("index.html", 'w')
f.write(index_page_html)
f.close()

papers_index_page_html = make_index_page_html(paper_notes, title="Papers", papers_page=True, subdir=PAPERS_DIR)
f = open("papers.html", 'w')
f.write(papers_index_page_html)
f.close()
