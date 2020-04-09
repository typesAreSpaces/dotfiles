syntax on

set tabstop=2 softtabstop=2
set shiftwidth=2
set expandtab
set smartindent
set nu
set smartcase
set noswapfile
set nobackup
set undodir=~/.vim/undodir
set undofile
set incsearch

highlight ColorColumn ctermbg=0 guibg=lightgrey

call plug#begin('~/.vim/plugged')

Plug 'ycm-core/YouCompleteMe'
Plug 'morhetz/gruvbox'
Plug 'dracula/vim' 
Plug 'jremmen/vim-ripgrep'
Plug 'tpope/vim-fugitive'
Plug 'leafgarland/typescript-vim'
Plug 'vim-utils/vim-man'
Plug 'lyuts/vim-rtags'
Plug 'git@github.com:kien/ctrlp.vim.git'
Plug 'neoclide/coc.nvim'
Plug 'mbbill/undotree'
Plug 'bohlender/vim-smt2' 
Plug 'vim-latex/vim-latex'
Plug 'FStarLang/VimFStar', {'for': 'fstar'}
Plug 'itchyny/lightline.vim'
Plug 'preservim/nerdtree'
Plug 'preservim/nerdcommenter'
Plug 'jeffkreeftmeijer/vim-numbertoggle'

call plug#end()

let mapleader=" "

nnoremap <C-J> <C-W><C-J>
nnoremap <C-K> <C-W><C-K>
nnoremap <C-L> <C-W><C-L>
nnoremap <C-H> <C-W><C-H>

nnoremap <silent> [b :bprevious<CR>
nnoremap <silent> ]b :bnext<CR>
nnoremap <silent> [B :bfirst<CR>
nnoremap <silent> ]B :bblast<CR>

nnoremap <silent> <Leader>gd :YcmCompleter GoTo<CR>
nnoremap <Leader>l :ls<CR>
nnoremap <silent> <Leader>gr :YcmCompleter GoToReferences<CR>

colorscheme dracula 
set background=dark

if executable('rg')
  let g:rg_derive_root='true'
end

let g:smt2_solver_command="z3 -smt2"
let g:smt2_solver_version_switch="4.8.8"

set laststatus=2
nnoremap <C-n> :NERDTreeToggle<CR>

set timeoutlen=1000 ttimeoutlen=0
set clipboard=unnamedplus

set number relativenumber
set nu rnu
