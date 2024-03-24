#!/bin/bash

./mdriver-dbg -d 2 -v 2 -f traces/syn-array-short.rep 
./mdriver-dbg -d 2 -v 2 -f traces/syn-string-short.rep 
./mdriver-dbg -d 2 -v 2 -f traces/syn-struct-short.rep  
./mdriver-dbg -d 2 -v 2 -f traces/syn-mix-short.rep 
./mdriver-dbg -d 2 -v 2 -f traces/ngram-fox1.rep 
./mdriver-dbg -d 2 -v 2 -f traces/syn-mix-realloc.rep 
./mdriver-dbg -d 2 -v 2 -f traces/syn-mix.rep