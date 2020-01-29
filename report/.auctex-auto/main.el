(TeX-add-style-hook
 "main"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("report" "twoside" "11pt" "openright")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("inputenc" "latin1") ("babel" "american") ("fontenc" "T1") ("datetime2" "useregional")))
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperref")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "href")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (TeX-run-style-hooks
    "latex2e"
    "sections/introduction"
    "report"
    "rep11"
    "inputenc"
    "babel"
    "a4"
    "latexsym"
    "amssymb"
    "amsmath"
    "epsfig"
    "fontenc"
    "mathptmx"
    "color"
    "epstopdf"
    "microtype"
    "hyperref"
    "datetime2"
    "lipsum")
   (TeX-add-symbols
    '("todo" 1))
   (LaTeX-add-labels
    "ch:main"
    "ch:conclusion")
   (LaTeX-add-bibliographies
    "refs"))
 :latex)

