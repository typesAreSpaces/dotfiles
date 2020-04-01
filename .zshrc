# If you come from bash you might have to change your $PATH.
# export PATH=$HOME/bin:/usr/local/bin:$PATH
export PATH=$HOME"/.opam/system/bin:"$PATH
export PATH="/usr/bin:"$PATH
export PATH="/$HOME/Documents/GithubProjects/cool-retro-term:"$PATH

# Path to your oh-my-zsh installation.
export ZSH="$HOME/.oh-my-zsh"

# Set name of the theme to load --- if set to "random", it will
# load a random theme each time oh-my-zsh is loaded, in which case,
# to know which specific one was loaded, run: echo $RANDOM_THEME
# See https://github.com/robbyrussell/oh-my-zsh/wiki/Themes
#ZSH_THEME="random"
ZSH_THEME="dracula"

# Set list of themes to pick from when loading at random
# Setting this variable when ZSH_THEME=random will cause zsh to load
# a theme from this variable instead of looking in ~/.oh-my-zsh/themes/
# If set to an empty array, this variable will have no effect.
# ZSH_THEME_RANDOM_CANDIDATES=( "robbyrussell" "agnoster" )

# Uncomment the following line to use case-sensitive completion.
# CASE_SENSITIVE="true"

# Uncomment the following line to use hyphen-insensitive completion.
# Case-sensitive completion must be off. _ and - will be interchangeable.
# HYPHEN_INSENSITIVE="true"

# Uncomment the following line to disable bi-weekly auto-update checks.
# DISABLE_AUTO_UPDATE="true"

# Uncomment the following line to automatically update without prompting.
# DISABLE_UPDATE_PROMPT="true"

# Uncomment the following line to change how often to auto-update (in days).
# export UPDATE_ZSH_DAYS=13

# Uncomment the following line if pasting URLs and other text is messed up.
# DISABLE_MAGIC_FUNCTIONS=true

# Uncomment the following line to disable colors in ls.
# DISABLE_LS_COLORS="true"

# Uncomment the following line to disable auto-setting terminal title.
# DISABLE_AUTO_TITLE="true"

# Uncomment the following line to enable command auto-correction.
# ENABLE_CORRECTION="true"

# Uncomment the following line to display red dots whilst waiting for completion.
# COMPLETION_WAITING_DOTS="true"

# Uncomment the following line if you want to disable marking untracked files
# under VCS as dirty. This makes repository status check for large repositories
# much, much faster.
# DISABLE_UNTRACKED_FILES_DIRTY="true"

# Uncomment the following line if you want to change the command execution time
# stamp shown in the history command output.
# You can set one of the optional three formats:
# "mm/dd/yyyy"|"dd.mm.yyyy"|"yyyy-mm-dd"
# or set a custom format using the strftime function format specifications,
# see 'man strftime' for details.
# HIST_STAMPS="mm/dd/yyyy"

# Would you like to use another custom folder than $ZSH/custom?
# ZSH_CUSTOM=/path/to/new-custom-folder

# Which plugins would you like to load?
# Standard plugins can be found in ~/.oh-my-zsh/plugins/*
# Custom plugins may be added to ~/.oh-my-zsh/custom/plugins/
# Example format: plugins=(rails git textmate ruby lighthouse)
# Add wisely, as too many plugins slow down shell startup.
plugins=(git)

source $ZSH/oh-my-zsh.sh

# User configuration

# export MANPATH="/usr/local/man:$MANPATH"

# You may need to manually set your language environment
# export LANG=en_US.UTF-8

# Preferred editor for local and remote sessions
# if [[ -n $SSH_CONNECTION ]]; then
#   export EDITOR='vim'
# else
#   export EDITOR='mvim'
# fi

# Compilation flags
# export ARCHFLAGS="-arch x86_64"

# Set personal aliases, overriding those provided by oh-my-zsh libs,
# plugins, and themes. Aliases can be placed here, though oh-my-zsh
# users are encouraged to define aliases within the ZSH_CUSTOM folder.
# For a full list of active aliases, run `alias`.
#
# Example aliases
# alias zshconfig="mate ~/.zshrc"
# alias ohmyzsh="mate ~/.oh-my-zsh"

alias second_home="cd /media/jose/4486d9bd-d3c3-4b92-9842-d38226a22c20/$HOME"
alias emacs="emacs -nw"
alias open="xdg-open"
alias utop="rlwrap ocaml"

alias semester="cd /$HOME/Documents/Current-Semester/PhD\ in\ Computer\ Science\ UNM/Semester\ 3"
alias masterThesis="cd /$HOME/Documents/GithubProjects/master-thesis/Software/Cpp/EUFInterpolantsZ3"
alias masterThesisPaperProject="cd /$HOME/Documents/GithubProjects/master-thesis/Write\ Ups/paper_project"
alias z3_dir="cd ~/Documents/GithubProjects/z3"
alias my_z3_dir="cd ~/Documents/GithubProjects/z3__"

alias bosqueProject="cd /$HOME/Documents/GithubProjects/BosqueLanguage && code . && cd ref_impl/src/verifier"
alias bosqueInstall="npm install && npm run-script build"
alias bosqueVerifier="node /$HOME/Documents/GithubProjects/BosqueLanguage/ref_impl/bin/verifier/testing/testing_collect_expressions.js"
alias gg="bosqueInstall && bosqueVerifier"
alias bosqueExec="node /$HOME/Documents/GithubProjects/BosqueLanguage/ref_impl/bin/test/app_runner.js"
alias gitDiscardChanges="git stash save --keep-index --include-untracked"
alias findCPPETAGS="find . -type f -iname \"*.[chS]p*\" | xargs etags -a"
alias vim="vim.gtk3"

function fstar(){
    fstar.exe "$1" --z3refresh --z3rlimit 20 --max_fuel 15 --max_ifuel 5
}

function fstar2(){
    fstar.exe "$1" --z3refresh --z3rlimit 30 --max_fuel 20 --max_ifuel 15
}

alias smtinterpol="java -jar ~/Documents/Apps/smtinterpol.jar"
# OPAM configuration
. /$HOME/.opam/opam-init/init.zsh > /dev/null 2> /dev/null || true
alias config='/usr/bin/git --git-dir=$HOME/.cfg/ --work-tree=$HOME'
