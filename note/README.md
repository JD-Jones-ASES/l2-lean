# The research note

`main.tex` is the research note on the theorems this repository proves: a two-fold Langford sequence
of order `l` and defect `d` exists exactly when `3l ≥ 2d − 1`, and for every `m` the counting bound
`(2m − 1)l ≥ 2d − 1` is necessary and attained, with the row `l = 1` and the cell `(6, 3)` showing it
is not sufficient for `m ≥ 3`. It also has every class table of the band families, and a section
on the linear relaxation for `m ≥ 3` that is not formalized. `main.pdf` is the built note; rebuild
it with `pdflatex -interaction=nonstopmode main.tex`, three passes.

`certificates/0033-rt057-two-fold-langford-all-cells/` holds the note's finite-data certificate: a
statement (`NOTES.md`) and two independent checkers, `verify.py` and `verify_second.py`, that use
only the Python standard library. Each rebuilds a two-fold sequence at every in-bound cell with
`l ≤ L` by the constructions of the proof and checks it from the definition. Replay from inside the
folder:

```sh
cd certificates/0033-rt057-two-fold-langford-all-cells
python verify.py 300
python verify_second.py 300
```

The first ends with a line beginning `VERDICT: ALL VERIFIED`, the second with one beginning
`VERDICT: PASS`; each takes fifteen to twenty seconds. `run_300.log` and `run_second_300.log` are
their outputs. With `--routes`, either script also writes the route of every cell to a JSON file
beside itself; with `--log`, `verify_second.py` also writes its output to `run_second_<L>.log`.

License: the note (`main.tex`, `main.pdf`) is [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/);
the certificate is [MIT](../LICENSE), like the rest of the repository.
