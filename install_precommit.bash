#!/bin/bash
if [[ -e .git/hooks/pre-commit ]]; then
    echo "pre commit file (.git/hooks/pre-commit) already exists"
    echo "please move it"
    exit 1
fi

cat > .git/hooks/pre-commit <<'END'
#!/bin/sh

set -e

mypy --strict .

find -name '*.py' | xargs autopep8 -d > /tmp/autopep8diff

[ "$(cat /tmp/autopep8diff)" != "" ] && cat /tmp/autopep8diff && exit 1

time -p pytest

exit 0
END
