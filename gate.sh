#!/bin/bash
# Gate for the Lean formalisation. It passes only if all of these hold:
#  * the sources contain no `sorry`, `admit`, `native_decide`, `axiom` keyword (anywhere,
#    including one on a line of its own), `#eval`, `run_cmd`, `initialize`, `IO`, or `debug.` option;
#  * the library builds without errors;
#  * the gate itself (not a file in the repo) generates the `#print axioms` report for each
#    REQUIRED theorem, and each report is present exactly once;
#  * every theorem depends only on Lean's standard axioms (propext, Classical.choice, Quot.sound).
# Lean wraps long axiom lists across several lines, so the output is flattened before parsing.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
NS="PrimitiveRootFamilies"
REQUIRED="chebyshev_residues not_dvd_9999 legendreSym_five_four_eq_one ten_isPrimitiveRoot"
SOURCES="PrimitiveRootFamilies/*.lean PrimitiveRootFamilies.lean"
[ -e .lake/packages/mathlib ] || lake exe cache get || { echo "FAIL: could not fetch Mathlib cache"; exit 1; }
if grep -nE "\bsorry\b|\badmit\b|native_decide|\baxiom\b|#eval|\brun_cmd\b|\binitialize\b|\bIO\b|\bdebug\." $SOURCES; then
  echo "FAIL: forbidden token"; exit 1; fi
build=$(lake build $NS 2>&1); bstatus=$?
printf '%s\n' "$build" | tail -3
[ "$bstatus" -eq 0 ] || { printf '%s\n' "$build"; echo "FAIL: build"; exit 1; }
# The axiom report is generated here, so no file in the repo can fake it.
chk=$(mktemp --suffix=.lean -p . .gatecheck_XXXX)
trap 'rm -f "$chk"' EXIT
{ echo "import $NS"; for t in $REQUIRED; do echo "#print axioms $NS.$t"; done; } > "$chk"
out=$(lake env lean "$chk" 2>&1); status=$?
printf '%s\n' "$out"
[ "$status" -eq 0 ] || { echo "FAIL: axiom report"; exit 1; }
echo "$out" | grep -qE "(^|:)[[:space:]]*error" && { echo "FAIL: Lean reported an error"; exit 1; }
flat=$(printf '%s\n' "$out" | awk '/^'"'"'/{if(buf!="")print buf; buf=$0; next} {buf=buf" "$0} END{if(buf!="")print buf}')
reports=$(printf '%s\n' "$flat" | grep -E "depends on axioms|does not depend on any axioms")
n=0
for t in $REQUIRED; do
  c=$(printf '%s\n' "$reports" | grep -cE "^'$NS\.$t' (depends on axioms|does not depend)")
  [ "$c" -eq 1 ] || { echo "FAIL: expected one axiom report for $t, found $c"; exit 1; }
  n=$((n+1))
done
[ "$(printf '%s\n' "$reports" | grep -c .)" -eq "$n" ] || { echo "FAIL: unexpected extra reports"; exit 1; }
printf '%s\n' "$reports" | grep "depends on axioms" | grep -qv '\]' && { echo "FAIL: unterminated axiom list"; exit 1; }
bad=$(printf '%s\n' "$reports" | grep "depends on axioms" | sed 's/.*depends on axioms: *\[//; s/\].*//' \
      | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u \
      | grep -vE '^(propext|Classical\.choice|Quot\.sound)$')
[ -n "$bad" ] && { echo "FAIL: nonstandard axioms: $bad"; exit 1; }
echo "PASS ($n theorems, standard axioms only)"
