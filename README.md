# leansnippets
Anything I prove in Lean which doesn't belong in the standard library or HoTT library, I put here.

See [propositional_truncation](propositional_truncation.hlean) for the construction of the propositional truncation from quotients.

You need to have [Lean 2](https://github.com/leanprover/lean2) to run this code. If the files do not compile with your version of Lean, try the following:

* If your version of Lean is outdated, update to `leanprover/lean2/master`
* Maybe I have local changes which are already incorporated here, but not yet merged to `leanprover/lean2/master`. Try `fpvandoorn/lean2/master` or `fpvandoorn/lean2/personal` (whichever is newer).
* It is possible that there was a change which broke some files in this repository without me realizing it. Try `fpvandoorn/lean/*commit*` where `*commit*` is the last commit before I've updated this repository. In this case, please also open an issue.