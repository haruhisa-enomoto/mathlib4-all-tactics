# All tactics in mathlib4
[**all-tactics.md**](all-tactics.md)

mathlib4 rev: c161d1800ce3788307e2d726b7a265549a1c04d7 (2023-09-06)

# How to obtain this?
1. Make a new Lean 4 project with mathlib4 (using `lake new project_name math`)
2. The following codes yields the docstrings of all mathlib4 tactics in *Message* in line 2, so copy and paste it in a new markdown file.
```
import Mathlib.Tactic
#help tactic
```
3. Replace `syntax "(.*?)".*?\[(.*)\]` (regex) with:
```
# $1
Defined in: `$2`

```
4. Delete `^  ` (regex).
5. Manually fix some tactics.
