#!/bin/bash

(test $# -lt 3) && (echo "too few arguments") && exit 0

APKDIR=$1
TRACEDIR=$2
RESULTDIR=$3

mkdir -p $RESULTDIR/ICCReport
resultlog=$RESULTDIR/ICCReport/log.ICCReport.all
> $resultlog
for orgapk in $APKDIR/*.apk
do
    packname=${orgapk##*/}
	if [ ! -s $TRACEDIR/$packname.logcat ];
	then
        echo $orgapk did not have trace.
		continue
	fi
	#rt=`cat lowcov_malware | awk '{print $1}' | grep -a -c "^${i}.apk.logcat$"`
	#if [ $rt -lt 1 ];then
		echo "result for $orgapk" >> $resultlog 2>&1
		/home/hcai/bin/getpackage.sh $orgapk >> $resultlog 2>&1
		sh ICCReport_rakib.sh \
			$orgapk \
			$TRACEDIR/$packname.logcat $RESULTDIR/ICCReport >> $resultlog 2>&1
	#fi
done

#mv /home/hcai/testbed/{gicc.txt,dataicc.txt,extraicc.txt,icclink.txt,icccov.txt,bothdataicc.txt} $RESULTDIR/ICCReport
#mv /home/hcai/testbed/iccfeatures.txt $RESULTDIR/ICCReport

exit 0

