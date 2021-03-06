" Vim syntax file
" Language:      Flow
" Maintainers:   Reed Oei <me@reedoei.com>
" Version: 0.1

" Quit if syntax file is already loaded
if version < 600
  syntax clear
elseif exists("b:current_syntax")
  finish
endif

let b:current_syntax = "flow"

syntax keyword transaction internal transaction view returns returning event private type is implementation of
syntax match specialTransactions "on create"
syntax match specialTransactions "on fail"
syntax match specialTransactions "on success"
syntax keyword import import
syntax keyword conditional if else only when then be such that where

syntax keyword distrSpecifiers everything

syntax match operator '[~&\|!=+\-*/>@<:%\[\]{}]\+'
syntax keyword stateCheck in
syntax keyword new new
syntax keyword boolOps and or not

syntax keyword specialKeywords try catch constant unique asset immutable fungible emit let consume consumable return total copy demote via var transformer pass
syntax keyword specialVars msg this one any nonempty empty one every

syntax match variable '\<[A-Z][A-Za-z0-9]*'

syn region multilineComment start="/\*"    end="\*/" contains=todo
syntax match comment "//.*$" contains=todo
syntax keyword todo contained TODO NOTE

syntax match num '\<#\?[-+]\?\d\+\.\?\d*'
syntax keyword constWords true false

syntax region string start='"' end='"' skip='\\"'
syntax region string start='\'' end='\'' skip='\\\''

syntax keyword type nat int bool bytes address string ether uint256 set linking map option list multiset link mapitem

syntax keyword contract contract state storage source sink pool interface
syntax keyword contractModifiers main

hi def link transaction Function
hi def link specialTransactions Statement
hi def link operator Operator
hi def link boolOps Operator
hi def link new Operator
hi def link stateCheck Operator
hi def link conditional Conditional
hi def link import PreProc

hi def link contract Function
hi def link contractModifiers Function
hi def link specialKeywords Identifier
hi def link specialVars Underlined
hi def link keywords Identifier
hi def link type Type

hi def link constWords Constant
hi def link distrSpecifiers Constant
hi def link num Number

hi def link todo Todo
hi def link multilineComment Comment

