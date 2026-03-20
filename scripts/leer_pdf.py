from proyecto_isabelle.parse import load_text

texto = load_text(
    "./data/raw/pdfs/teoremas_combinatoriales.pdf", pages=[15, 16, 17, 18]
)

print(texto[:5000])
