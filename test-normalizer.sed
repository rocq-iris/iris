# locations in Fail, depends on local file path
/^File/d
# Ltac2 printing changed (https://github.com/rocq-prover/rocq/pull/18560)
s/StringToIdent\.([a-zA-Z]+) \((.*)\)/StringToIdent.\1 \2/
