#!/bin/bash
source config.sh

(test $# -lt 3) && (echo "too few arguments") && exit 0

indir=$1
linkage=$2
resdir=$3
APKDIR=$TOOLHOME/$indir/pairs/$linkage
TRACEDIR=$TOOLHOME/singleappTrace_$linkage

resultdir=$TOOLHOME/$resdir/securityReport/$linkage
mkdir -p $resultdir
resultlog=$resultdir/log.securityReport.all.$linkage
> $resultlog
for ((i=1;i<=$APPPAIRNUM;i++))
do
	if [ ! -d $APKDIR/$i ];then continue; fi
	echo "result for $linkage $i/s.apk" >> $resultlog 2>&1
	$TOOLHOME/apkmng/getpackage.sh $APKDIR/$i/s.apk >> $resultlog 2>&1
	bash $TOOLHOME/securityReport.sh \
		$APKDIR/$i/s.apk \
		$TRACEDIR/$i-s.logcat >> $resultlog 2>&1

	echo "result for $linkage $i/t.apk" >> $resultlog 2>&1
	$TOOLHOME/apkmng/getpackage.sh $APKDIR/$i/t.apk >> $resultlog 2>&1
	bash $TOOLHOME/securityReport.sh \
		$APKDIR/$i/t.apk \
		$TRACEDIR/$i-t.logcat >> $resultlog 2>&1
done

mv $TOOLHOME/{srcsink.txt,src.txt,sink.txt,callback.txt,lifecycleMethod.txt,eventHandler.txt,securityfeatures.txt} \
	$resultdir

exit 0
