globalVariables(".SD")
globalVariables(".")

aggr <- function(x, clusters){
  #seems like lapply(.SD, sum) on data.table drops 
  #columns with identical names, thus ensure that no identical names
  colnames(x) <- NULL 
  temp <- data.table(x)
  temp <- as.matrix(temp[, j=lapply(.SD, sum), by=clusters])[, -1]

}  

bounds <- function(data, Z, X, Y){

  if(is.data.frame(data)){
    p00.0 <- sum(data[, Y]==0 & data[, X]==0 & data[, Z]==0)/sum(data[, Z]==0)
    p00.1 <- sum(data[, Y]==0 & data[, X]==0 & data[, Z]==1)/sum(data[, Z]==1)
    p01.0 <- sum(data[, Y]==0 & data[, X]==1 & data[, Z]==0)/sum(data[, Z]==0)
    p01.1 <- sum(data[, Y]==0 & data[, X]==1 & data[, Z]==1)/sum(data[, Z]==1)
    p10.0 <- sum(data[, Y]==1 & data[, X]==0 & data[, Z]==0)/sum(data[, Z]==0)
    p10.1 <- sum(data[, Y]==1 & data[, X]==0 & data[, Z]==1)/sum(data[, Z]==1)
    p11.0 <- sum(data[, Y]==1 & data[, X]==1 & data[, Z]==0)/sum(data[, Z]==0)
    p11.1 <- sum(data[, Y]==1 & data[, X]==1 & data[, Z]==1)/sum(data[, Z]==1)
  }
  else{
    p00.0 <- data["p00.0"]
    p00.1 <- data["p00.1"]
    p01.0 <- data["p01.0"]
    p01.1 <- data["p01.1"]
    p10.0 <- data["p10.0"]
    p10.1 <- data["p10.1"]
    p11.0 <- data["p11.0"]
    p11.1 <- data["p11.1"]
  }
  
  p0 <- c(max(c(p10.0+p11.0-p00.1-p11.1,
    p10.1,
    p10.0,
    p01.0+p10.0-p00.1-p01.1)), 
    min(c(p01.0+p10.0+p10.1+p11.1,
    1-p00.1,
    1-p00.0,
    p10.0+p11.0+p01.1+p10.1)))
  p1 <- c(max(c(p11.0,
    p11.1,
    -p00.0-p01.0+p00.1+p11.1,
    -p01.0-p10.0+p10.1+p11.1)), 
    min(c(1-p01.1,
    1-p01.0,
    p00.0+p11.0+p10.1+p11.1,
    p10.0+p11.0+p00.1+p11.1)))
  
  RD <- c(max(c(p11.1+p00.0-1,
    p11.0+p00.1-1,
    p11.0-p11.1-p10.1-p01.0-p10.0,
    p11.1-p11.0-p10.0-p01.1-p10.1,
    -p01.1-p10.1,
    -p01.0-p10.0,
    p00.1-p01.1-p10.1-p01.0-p00.0,
    p00.0-p01.0-p10.0-p01.1-p00.1)), 
    min(c(1-p01.1-p10.0,
    1-p01.0-p10.1,
    -p01.0+p01.1+p00.1+p11.0+p00.0,
    -p01.1+p11.1+p00.1+p01.0+p00.0,
    p11.1+p00.1,
    p11.0+p00.0,
    -p10.1+p11.1+p00.1+p11.0+p10.0,
    -p10.0+p11.0+p00.0+p11.1+p10.1)))
    
  return(list(p0=p0, p1=p1, RD=RD))

}

tsls <- function(fitX, fitY, control=FALSE, data, clusterid){
  
  #preliminaries

  n <- nrow(data)
  if(!missing(clusterid))
    ncluster <- length(unique(data[, clusterid]))

  #collect features of fitX

  designX <- model.matrix(object=fitX)
  resX <- residuals(object=fitX, type="response")
  nX <- length(fitX$coef)
   
  #estimate

  Xhat <- predict(object=fitX, type="response")
  X <- as.character(fitX$formula[2])
  data.Xhat <- data
  data.Xhat[, X] <- Xhat
  if(control){
    data.Xhat$R <- resX
    fitY <- update(object=fitY, formula=~.+R, data=data.Xhat)
  }
  else{
    fitY <- update(object=fitY, data=data.Xhat)
  }
  est <- fitY$coef
  #collect features of fitY

  designY <- model.matrix(object=fitY)
  resY <- residuals(object=fitY, type="response") 
  nY <- length(fitY$coef)
 
  #variance  

  UX <- resX*designX 
  UY <- resY*designY
  U <- cbind(UX, UY)
  if(!missing(clusterid))
      U <- aggr(x=U, clusters=data[, clusterid])
  J <- var(U, na.rm=TRUE)
  IX <- cbind(-solve(summary(object=fitX)$cov.unscaled)/n,
    matrix(0, nrow=nX, ncol=nY))    
  UYfunc <- function(b){
    Xhat <- as.vector(family(fitX)$linkinv(designX%*%matrix(b))) 
    data.Xhat[, X] <- Xhat  
    if(control)
      data.Xhat$R <- data[, X]-Xhat
    designY <- model.matrix(object=fitY$formula, data=data.Xhat)
    Yhat <- as.vector(family(fitY)$linkinv(designY%*%matrix(est)))
    resY <- fitY$y-Yhat
    UY <- resY*designY  
    colMeans(UY)
  } 
  IY <- cbind(jacobian(func=UYfunc, x=fitX$coef),
    -solve(summary(object=fitY)$cov.unscaled)/n)    
  I <- rbind(IX, IY)
  if(missing(clusterid))
    vcov <- (solve(I)%*%J%*%t(solve(I))/n)
  else
    vcov <- (solve(I)%*%J%*%t(solve(I))*ncluster/n^2)
  vcov <- vcov[(nX+1):(nX+nY), (nX+1):(nX+nY)]
  rownames(vcov) <- names(est)
  colnames(vcov) <- names(est)
  
  result <- list(call=match.call(), est=est, vcov=vcov)
  class(result) <- "tsls"

  return(result)
  
}

summary.tsls <- function(object, digits=max(3L, getOption("digits")-3L), ...) {
  s.err <- sqrt(diag(as.matrix(object$vcov)))
  zvalue <- object$est/s.err
  pvalue <- 2 * pnorm(-abs(zvalue))
  coef.table <- as.matrix(cbind(object$est, s.err, zvalue, 
        pvalue))
  dimnames(coef.table) <- list(names(object$est), c("Estimate", 
      "Std. Error", "z value", "Pr(>|z|)"))
  ans <- list(call = object$call, coefficients = coef.table)
  class(ans) <- "summary.tsls"
  return(ans)
}

print.summary.tsls <- function(x, digits=max(3L, getOption("digits")-3L), 
  signif.stars=getOption("show.signif.stars"), ...) {
  cat("\nCall:  ", "\n", paste(deparse(x$call), sep="\n", collapse="\n"), 
      "\n", sep="")
  cat("\nCoefficients:", "\n")
  printCoefmat(x$coefficients, digits=digits, signif.stars=signif.stars, 
    na.print = "NA", ...)
  cat("\n") 
}

