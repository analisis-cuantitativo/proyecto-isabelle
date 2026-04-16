import json

from proyecto_isabelle.util.constants import ROOT_DIR

PROOFNET_DIR = ROOT_DIR / "data" / "raw" / "proofnet"
proofnet_files = PROOFNET_DIR.glob("*.jsonl")

files_to_save = []
for path_ in proofnet_files:
    with path_.open() as fp:
        files_to_save.extend([json.loads(line) for line in fp.readlines()])

for file_to_save in files_to_save:
    filename = file_to_save["id"].replace("|", "-")
    with open(
        ROOT_DIR / "data" / "exercises" / f"{filename}.md",
        "w",
    ) as fp:
        fp.write(file_to_save["nl_statement"])

    with open(ROOT_DIR / "data" / "exercises_with_proof" / f"{filename}.md", "w") as fp:
        fp.write(
            file_to_save["nl_statement"] + "\n\nProof:\n" + file_to_save["nl_proof"]
        )
