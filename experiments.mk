TOOL=$(shell pwd)/../NaTT.sh	# this is ugly!

test: NaTT
	TOOL=$(PWD)/NaTT.sh; \
	cd ~/tpdb/trs; \
	if [ -e tmp_result ]; then rm tmp_result; fi; \
	while read f; do \
		$$TOOL -V $$f | tee -a tmp_result; \
		if grep -q YES tmp_result; then echo WRONG!; exit 1; fi;\
	done < nonterm.list; \
	grep -c NO tmp_result; \
	rm tmp_result

MK_PROOF=\
	mkdir $@;\
	mkdir $@/proofs

L=\
	${MK_PROOF};\
	${TOOL} -p:"$@/proofs" ${TRS} ${PRE}

R=${POST} > $@/results.txt

#
# existing methods
#
TRIV:
	$L $R

LPO:
	$L LPO $R
MPO:
	$L LPO -Lex -mset $R
RPO:
	$L LPO -mset $R

KBO:
	$L KBO $R
TKBOb:
	$L KBO -c:b $R
TKBOt:
	$L KBO -c:t $R
TKBO:
	$L KBO -reset -w:3 -c:3 $R

POLOs:
	$L POLO $R
POLOsi:
	$L POLO -w:neg $R
POLOm:
	$L POLO -a:max $R
POLOmi:
	$L POLO -a:max -w:neg $R
POLOsm:
	$L POLO -a:mpol $R
POLOsmi:
	$L POLO -a:mpol -w:neg $R
POLOtmi:
	$L POLO -a:mpol -w:neg -c:t $R
POLOms:
	$L POLO -a:max -mp $R
POLOb:
	$L POLO -c:b $R
POLObi:
	$L POLO -c:b -w:neg $R
POLObm:
	$L POLO -a:mpol -c:b $R
POLObmi:
	$L POLO -a:mpol -w:neg -c:b $R
MAT2b:
	$L POLO --dim:2 -c:b $R
POLOq:
	$L POLO -c:q $R
POLOt:
	$L POLO -c:t $R
POLOp:
	$L POLO -reset -w:3 -c:3 $R
POLOpm:
	$L POLO -reset -a:mpol -w:3 -c:3 $R
MAT2:
	$L POLO -reset --dim:2 -w:3 -c:3 $R

#
# WPO
#
WPOs:
	$L WPO -a:pol $R
WPOs+:
	$L WPO -a:pol -Z $R
WPOm:
	$L WPO -a:max $R
WPOsm:
	$L WPO -a:mpol $R
WPOsm+:
	$L WPO -a:mpol -Z $R
WPOb:
	$L WPO -a:pol -c:b $R
WPObm:
	$L WPO -a:mpol -c:b $R
WPOtm:
	$L WPO -a:mpol -c:t $R
WPOp:
	$L WPO -a:pol -w:3 -c:3 $R
WPOpm:
	$L WPO -a:mpol -w:3 -c:3 $R
WPOmat2:
	$L WPO -a:pol -dim:2 -w:3 -c:3 $R

#
# Partial Status
#
KBOpS:
	$L KBO -s:p $R
TKBOpS:
	$L KBO -reset -c:3 -w:3 -s:p $R
KBOpS-min:
	$L KBO -s:p -min $R
KBOpS-max:
	$L KBO -s:p -max $R
KBOpS-minmax:
	$L KBO -s:p -min -max $R
WPOpSb:
	$L WPO -s:p $R
WPOpSb+:
	$L WPO -s:p -Z $R
WPOpSb-min:
	$L WPO -s:p -min $R
WPOpSb-minmax:
	$L WPO -s:p -min -max $R
WPOpSbm:
	$L WPO -s:p -a:mpol -c:b $R
WPOpStm:
	$L WPO -s:p -a:mpol -c:t $R
WPOpSms:
	$L WPO -s:p -a:max -mp:2 $R
WPOpSbm-min:
	$L WPO -s:p -a:mpol -min $R
WPOpSbm-minmax:
	$L WPO -s:p -a:mpol -min -max $R
WPOpSm:
	$L WPO -s:p -a:max $R
WPOpSm-min:
	$L WPO -s:p -a:max -min $R
WPOpSm-minmax:
	$L WPO -s:p -a:max -min -max $R
WPOpSmat2b:
	$L WPO -s:p -dim:2 -c:b $R
WPOpSmat2:
	$L WPO -s:p -dim:2 -w:3 -c:3 $R

WPOpSsi:
	$L WPO -s:p -w:neg $R
WPOpSmi:
	$L WPO -s:p -sp:neg -a:max $R
WPOpSsmi:
	$L WPO -s:p -w:neg -sp:neg -a:mpol $R

WPOpSp:
	$L WPO -s:p -w:3 -c:3 $R
WPOpSpm:
	$L WPO -s:p -a:mpol -w:3 -c:3 $R
WPOpSp-minmax:
	$L WPO -s:p -w:3 -c:3 -min -max $R
WPOpSq:
	$L WPO -s:p -c:q $R
WPOpSq-minmax:
	$L WPO -s:p -c:q -min -max $R
WPOpSqm-minmax:
	$L WPO -s:p -a:mpol -c:q -min -max $R


# Some AC-KBO variants
S90:
	$L KBO -ac:S90 $R
KV03:
	$L KBO -ac:KV03 $R
S90i:
	$L KBO -ac:S90i $R
KV03i:
	$L KBO -ac:KV03i $R
