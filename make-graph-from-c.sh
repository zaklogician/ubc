#! /bin/bash

# Original written by Yanyan Shen
# Fixed up by Mathieu Paturel (Nov 2022)

set -eux
script_name="$0"

show_help(){
    set +x

    message="${1:-}"
    if ! [ -z "$message" ]; then
        echo
        echo "$message"
        echo
    fi

    echo "Usage: $script_name <c_input_file> [output_file]"
    echo
    echo "Uses the L4V C parser and AsmRefine to extract the"
    echo "GraphLang representation of \$c_input_file."
    echo "Writes the result to CFunctions.txt, unless"
    echo "\$output_file is specified."

    exit 1
}

if [ $# -lt 1 -o $# -gt 2 ]; then
    show_help "Expected 1 or 2 arguments, got $#."
fi

c_file="$(realpath "$1")"
output_file="$(realpath "${2:-"${1%.*}.txt"}")"

L4V_ARCH="${L4V_ARCH:?Must set L4V_ARCH}"
TV_ROOT="${TV_ROOT:?Must set TV_ROOT.

TV_ROOT should point to a sync'd and init'd verification checkout, i.e. it
should point to the parent directory of l4v, graph-refine, HOL4, etc.}"
TV_ROOT="$(realpath "${TV_ROOT}")"

THY="$(cat <<END
theory "tmp"
imports
    "CParser.CTranslation"
    "AsmRefine.GlobalsSwap"
    "AsmRefine.SimplExport"
begin
declare [[populate_globals=true]]
typedecl machine_state
typedecl cghost_state
install_C_file "input.c"
  [machinety=machine_state, ghostty=cghost_state]
setup \\<open>DefineGlobalsList.define_globals_list_i
  "input.c" @{typ globals}\\<close>
locale target
  = input_global_addresses
begin
ML \\<open>
emit_C_everything_relative @{context}
  (CalculateState.get_csenv @{theory} "input.c" |> the)
  "result.txt" "" (* in older version of the function,
                     this last parameter (prefix) wasn't there,
                     and thus the function doesn't end up getting called*)
\<close>
end
end
END
)"
ROOT="$(cat <<END
session MySimplExport = AsmRefine +
    theories "tmp"
END
)"

TMP_DIR="$(mktemp -d)"
# TMP_DIR="/tmp/foo"
trap 'rm -rf -- "$TMP_DIR"' EXIT

pushd "$TMP_DIR"
cp "$c_file" input.c
echo -n "$THY" > tmp.thy
echo -n "$ROOT" > ROOT
echo "TV_ROOT $TV_ROOT"

# if gcc can't compile it, then isabelle won't be able to parse it
if ! gcc -Wall -Werror -Wextra "$c_file" -o "$TMP_DIR/a.out" -c
then
    # exit 0
    echo keep going
else
    rm "$TMP_DIR/a.out"
fi


# "$TV_ROOT"/isabelle/bin/isabelle build -d "$TV_ROOT"/l4v -D . -c
# cp result.txt "$output_file"

# login to work machine, it's bigger so faster :)
ssh vb-101 "rm -rf ~/.cparser-conversion"
scp -r "$TMP_DIR" vb-101:.cparser-conversion
ssh vb-101 "env L4V_ARCH='$L4V_ARCH' ~/verification/isabelle/bin/isabelle build -d ~/verification/l4v -D .cparser-conversion -c"
scp vb-101:.cparser-conversion/result.txt "$output_file"

popd
