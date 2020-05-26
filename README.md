# How to run (jankly):

1. `cabal repl`.
2. If you want to run reverse mode, enter `:l Reverse.hs`. Otherwise, go to 3.
3. `:main <pass|python> prog.fut`. Use `pass` to generate the internal representation of a the differentiated version of `prog.fut`. Use `python` to spit out Python code. (Which can then be manually run to test outputs.)