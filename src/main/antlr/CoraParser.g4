/**************************************************************************************************
 Copyright 2019, 2022, 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

/** This is a parser for the default Cora input format. */
parser grammar CoraParser;

@header {
  package cora.parsers;
}

options {
  tokenVocab = CoraLexer;
}

@parser::members {
}

constant            : IDENTIFIER
                    | STRING
                    ;

/*** Parsing types ***/

type                : constant
                    | lowarrowtype
                    | higherarrowtype
                    | BRACKETOPEN type BRACKETCLOSE
                    ;
lowarrowtype        : constant typearrow type ;
higherarrowtype     : BRACKETOPEN type BRACKETCLOSE typearrow type ;

typearrow           : ARROW
                    | TYPEARROW
                    ;

onlytype            : type EOF ;

declaration         : constant DECLARE type ;

/*** Parsing terms ***/

term                : constant
                    | constant BRACKETOPEN BRACKETCLOSE
                    | constant BRACKETOPEN term commatermlist
                    | abstraction
                    | BRACKETOPEN abstraction BRACKETCLOSE BRACKETOPEN term commatermlist
                    ;

abstraction         : LAMBDA binderlist DOT term
                    ;

commatermlist       : BRACKETCLOSE
                    | COMMA term commatermlist
                    ;
binderlist          : binder
                    | binder COMMA binderlist
                    ;
binder              : IDENTIFIER
                    | IDENTIFIER DECLARE type
                    ;

onlyterm            : term EOF ;

/*** Parsing rules ***/

simplerule          : term ARROW term
                    | term ARROW term BRACEOPEN declaration* BRACECLOSE
                    ;

/*** The whole program ***/

program             : simplerule program
                    | declaration program
                    |
                    ;

input               : program EOF ;

/*
sortdec             : SORT constant BRACEOPEN constant+ BRACECLOSE
                    | SORT constant
                    ;

term                : constant+
                    | constant* BRACKETOPEN termlist BRACKETCLOSE
                    | constant* BRACKETOPEN termlist BRACKETCLOSE term
                    ;

termlist            : term
                    | term COMMA termlist
                    ;
*/

