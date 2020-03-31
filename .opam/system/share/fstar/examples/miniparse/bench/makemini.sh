#!/bin/bash

set -ue

ctors () {
	for i in $(seq 1 $SIZE); do
		echo -n "| C$i "
	done
}

make1 () {
	FILE=$1
	MODULENAME=${FILE/.fst/}
	SIZE=$2
	FACTOR=$3
	SEED=$4
	POLICY=$5

	CTORS=$(ctors $SIZE)

	FLATMODULE=$(echo $MODULENAME | tr -d '.')

	cat MiniStub.fst | sed "s/__MODULE__/${MODULENAME}/g" \
			 | sed "s/__SUFFIX__/${FLATMODULE}/g" \
			 | sed "s/__SIZE__/${SIZE}/g" \
			 | sed "s/__CTORS__/${CTORS}/g" \
			 | sed "s/__FACTOR__/${FACTOR}/g" \
			 | sed "s/__SEED__/${SEED}/g" \
			 | sed "s/__POLICY__/${POLICY}/g" \
			 > $FILE
	cat MiniStub.fsti | sed "s/__MODULE__/${MODULENAME}/g" \
			 | sed "s/__SUFFIX__/${FLATMODULE}/g" \
			 | sed "s/__SIZE__/${SIZE}/g" \
			 | sed "s/__CTORS__/${CTORS}/g" \
			 | sed "s/__FACTOR__/${FACTOR}/g" \
			 | sed "s/__SEED__/${SEED}/g" \
			 | sed "s/__POLICY__/${POLICY}/g" \
			 > ${FILE}i
}

abort () {
	echo "expected input Bench.MiniParse.Size(SIZE).Factor(Factor).Seed(SEED).(SMT/Goal).fst" &>2
}

IFS='.' read -r -a array <<< "$1"

if ! [ x"${array[0]}" == x"Bench" ]; then
	abort
fi
if ! [ x"${array[1]}" == x"MiniParse" ]; then
	abort
fi

SIZE="${array[2]}"
SIZE="${SIZE/Size/}"

FACTOR="${array[3]}"
FACTOR="${FACTOR/Factor/}"

SEED="${array[4]}"
SEED="${SEED/Seed/}"

POLICY="${array[5]}"

make1 "$1" "$SIZE" "$FACTOR" "$SEED" "$POLICY"
