# Congruent numbers

A Lean 4 formalization of the elementary theory of the congruent number
problem, following the plan at
[FormalCommons/congruent-numbers-plan](https://github.com/FormalCommons/congruent-numbers-plan).
It builds on [Tau Ceti](https://github.com/TauCetiProject/TauCeti) and Mathlib.

This is the first experiment with [fc-worker](https://github.com/FormalCommons/fc-worker):
AI agents work on this repository's issues, open pull requests, and review them,
and GitHub's merge queue merges the approved ones. Issues and pull requests
from people outside the project are not worked on by the agents.

```sh
lake exe cache get
lake build --wfail
```

Conventions for contributors, human or not, are in [AGENTS.md](AGENTS.md).
