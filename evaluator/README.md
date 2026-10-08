# Evaluator of the TRIEL core

`generated/TRIEL.hs` is exported by Isabelle from [`formal/core/TRIEL_Exec.thy`](../formal/core/TRIEL_Exec.thy) and must not be edited. CI checks that it is exactly what `isabelle build -e -D formal/core` produces. `Main.hs` reads the input and prints the report; every verdict is computed by the exported function `run` (`formal/core/CORE.md`, section 10).

Build with GHC (checked with 9.6.7; only `base` is needed):

```bash
ghc -O1 -ievaluator/generated -outputdir evaluator/build -o evaluator/triel-eval evaluator/Main.hs
```

Run a scenario through the translator and the evaluator:

```bash
python3 parser/triel_eval.py examples/core/scenarios/deadline_cure_ok.scn
```

The input format is described at the top of `Main.hs`, the scenario and report formats in [`examples/core/README.md`](../examples/core/README.md).
