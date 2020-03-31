# Load the environment variables
. /home/jose/.opam/opam-init/variables.sh > /dev/null 2> /dev/null || true

# Load the auto-complete scripts
if tty -s >/dev/null 2>&1; then
  . /home/jose/.opam/opam-init/complete.zsh > /dev/null 2> /dev/null || true
fi

# Load the opam-switch-eval script
if tty -s >/dev/null 2>&1; then
  . /home/jose/.opam/opam-init/switch_eval.sh > /dev/null 2> /dev/null || true
fi

