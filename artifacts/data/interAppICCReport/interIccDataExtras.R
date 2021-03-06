#!/bin/Rscript

require(graphics)

args=commandArgs(trailingOnly=TRUE)
if (length(args)<1) {
	stop("too few arguments")
	exit
}

fndata=args[1]
tdata=read.table(file=fndata)

deinterICC<- matrix(NA, nrow=nrow(tdata), ncol=ncol(tdata)/2)
#print(paste("row=",nrow(tdata),"col=",ncol(tdata)))

f.per <- function (x,y) {
	if (y<1e-10) return (0)
	return (x/y*100)
}

r=1
inv=1
for(i in seq(1,nrow(tdata),1)) {
	dinterICC=sum(tdata[i,1:8])
	if (dinterICC<1e-10) {
		inv<-inv+1
		next
	}

	curdeinterICC<- c(f.per(tdata[i,1]+tdata[i,2],dinterICC), f.per(tdata[i,3]+tdata[i,4],dinterICC), f.per(tdata[i,5]+tdata[i,6],dinterICC), f.per(tdata[i,7]+tdata[i,8],dinterICC))
	deinterICC[r,] <- curdeinterICC

	r <- r+1
}

print(paste(inv," invalid data points ignored."))

colors<-c("red","green","blue","darkorange") #,"black","yellow","darkorange","darkorchid","gold4","darkgrey")

pdf("./deinterICC.pdf")
boxplot(deinterICC, names=c("int_ex","int_im","ext_ex","ex_im"),col=colors,ylab="percentage")
meandeinterICC <- (colMeans(deinterICC, na.rm=TRUE))
points(meandeinterICC, col="gold", pch=18, cex=1.5)

#dev.off


