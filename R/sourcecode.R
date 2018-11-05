globalVariables(c(".", ".SD", "p00.0", "p00.1", "p00.2",
  "p01.0", "p01.1", "p01.2",
  "p10.0", "p10.1", "p10.2",
  "p11.0", "p11.1", "p11.2"))
  
aggr <- function(x, clusters){
  #seems like lapply(.SD, sum) on data.table drops 
  #columns with identical names, thus ensure that no identical names
  colnames(x) <- NULL 
  temp <- data.table(x)
  temp <- as.matrix(temp[, j=lapply(.SD, sum), by=clusters])[, -1]

} 

ah <- function(formula, data, weights, robust=FALSE){ 

  if(missing(weights))
    weights <- rep(1, nrow(data))
  mf <- model.frame(formula=formula, data=data)
  incl.names <- rownames(mf)
  incl.rows <- match(incl.names, rownames(data))  
  data <- data[incl.rows, ]
  weights <- weights[incl.rows]
  surv <- mf[, 1]
  X <- model.matrix(object=formula, data=data)[, -1, drop=FALSE]
  fit <- ahaz(surv=surv, X=X, weights=weights, robust=robust)
  fit$call <- match.call()
  fit$formula <- formula
  coef <- solve(fit$D, fit$d)
  coeff.names <- colnames(X)
  names(coef) <- coeff.names
  fit$coefficients <- coef
  vcov <- solve(fit$D)%*%fit$B%*%solve(fit$D)
  rownames(vcov) <- coeff.names
  colnames(vcov) <- coeff.names
  fit$vcov <- vcov
  fit$incl <- incl.names
  class(fit) <- c("ah", "ahaz")
  return(fit) 
   
}

confint.ivmod <- function(object, parm, level=0.95, ...){
  
  est <- object$est
  se <- sqrt(diag(object$vcov))
  qqq <- abs(qnorm((1-level)/2))
  lower <- est-qqq*se
  upper <- est+qqq*se
  ci <- cbind(lower, upper)
  return(ci)
  
}

#computes estimating function for each subject
estfun <- function(b, Z, X, Y, type, fitZ, fitY, npsi, nZ, nY, 
  designpsi, designZ, designY, weights, data, y, t1, nuisance){

  n <- nrow(data)
  psi <- b[1:npsi]
  g <- designpsi*data[, X]
  lppsi <- as.vector(g%*%psi)
  if(type=="identity")
    Y0hat <- data[, Y]-lppsi
  if(type=="log")
    Y0hat <- data[, Y]*exp(-lppsi)
  if(type=="logit"){
    bY <- b[(npsi+nZ+1):(npsi+nZ+nY)]
    lpY <- as.vector(designY%*%bY)
    Y0hat <- plogis(lpY-lppsi)  
  }
  if(type=="coxph"){
    if(class(fitY)[1]=="survfit"){
        H <- b[(npsi+nZ+1):(npsi+nZ+nY)]
        vars <- all.vars(fitY$call$formula[[3]])
        strata.all <- strata(data[, vars, drop=FALSE])
        Y0hat <- exp(-H[strata.all]*exp(-lppsi))  
      }
    if(class(fitY)[1]=="coxph"){
      bY <- b[(npsi+nZ+1):(npsi+nZ+nY-1)]
      H0 <- b[npsi+nZ+nY]
      lpY <- as.vector(designY%*%bY)  
      Y0hat <- exp(-H0*exp(lpY-lppsi))
    }
  }
  bZ <- b[(npsi+1):(npsi+nZ)]
  d <- designpsi*(data[, Z]-as.vector(family(fitZ)$linkinv(designZ%*%bZ)))
  Upsi <- weights*d*Y0hat
  Upsi[is.na(Upsi)] <- 0

  if(nuisance){
    resZ <- expand(residuals(object=fitZ, type="response"), rownames(data)) 
    UZ <- weights*designZ*resZ
    UZ[is.na(UZ)] <- 0
    if(type=="identity" | type=="log")
      UY <- NULL
    if(type=="logit"){
      resY <- expand(residuals(object=fitY, type="response"), rownames(data))
      UY <- weights*designY*resY 
      UY[is.na(UY)] <- 0 
    }
    if(type=="coxph"){
      if(class(fitY)[1]=="survfit"){
        ss <- summary(fitY)
        strata <- ss$strata
        n.strata <- summary(strata)
        nY <- length(n.strata)
        strata.names <- names(n.strata)
        time <- ss$time
        nevent <- ss$n.event
        nrisk <- ss$n.risk  
        dH <- nevent/nrisk
        names(dH) <- paste(time, strata)
        dHvar <- dH/nrisk
        vars <- all.vars(fitY$call$formula[[3]])
        strata.all <- strata(data[, vars, drop=FALSE])  
        Hi <- matrix(nrow=n, ncol=nY) 
        breaks <- c(0, cumsum(n.strata))
        for(k in 1:nY){
          incl <- (breaks[k]+1):breaks[k+1] 
          Hfunvar <- stepfun(time[incl], c(0, cumsum(dHvar[incl]))) 
          temp <- n*dH[incl]/nevent[incl]*(time[incl]<=y)
          Hi[, k] <- temp[match(paste(data[, Y], strata.all), names(temp))]
          Hi[is.na(Hi[, k]), k] <- 0
          sk <- strata.names[k]
          incl <- which(strata.all==sk)
          dMcorrection <- n*Hfunvar(pmin(y, data[incl, Y]))
          if(!is.null(t1))
            dMcorrection <- dMcorrection-n*Hfunvar(data[incl, t1])*(data[incl, t1]<y)
          else
            dMcorrection <- n*Hfunvar(pmin(y, data[incl, Y]))
          Hi[incl, k] <- Hi[incl, k]-dMcorrection 
        }
        UY <- Hi
        UY[is.na(UY)] <- 0  
      }
      if(class(fitY)[1]=="coxph"){
        resY <- expand(residuals(object=fitY, type="score"), rownames(data))
        fitY.detail <- coxph.detail(object=fitY)
        time <- fitY.detail$time
        nevent <- fitY.detail$nevent
        nrisk <- fitY.detail$nrisk
        dH0 <- fitY.detail$hazard
        names(dH0) <- time
        dH0var <- dH0/nrisk
        H0funvar <- stepfun(time, c(0, cumsum(dH0var)))   
        H0i <- n*expand(dH0/nevent*(time<=y), data[, Y]) 
        H0i[is.na(H0i)] <- 0
        Hfunvar <- stepfun(time, c(0, cumsum(dH0var)))
        dMcorrection <- n*H0funvar(pmin(y, data[, Y]))
        if(!is.null(t1))
          dMcorrection <- dMcorrection-n*Hfunvar(data[, t1])*(data[, t1]<y) 
        H0i <- H0i-dMcorrection 
        UY <- cbind(weights*resY, H0i)
        UY[is.na(UY)] <- 0  
      }
    }
    U <- cbind(Upsi, UZ, UY)
  }
  else{
    U <- Upsi
  }  
  return(U)
  
}

estfunSums <- function(object, psi){
 
  #extract stuff from fitted gest object 
  input <- object$input
  data <- input$data
  n <- nrow(data)
  Z <- input$Z
  X <- input$X
  Y <- input$Y
  if(class(object)[1]=="ivglm"){
    if(object$input$link=="identity")
      type <- "identity"
    if(object$input$link=="log")
      type <- "log"
    if(object$input$link=="logit")
      type <- "logit"
    fitY <- input$fitY
  }
  if(class(object)[1]=="ivcoxph"){
    type <- "coxph"
    fitY <- input$fitT
  }
  if(class(object)[1]=="ivah")
    type <- "ah"
  formula <- input$formula
  y <- object$t
  fitZ <- object$fitZ
  
  #collect useful stuff  
  stuff <- utilityfun(Z=Z, X=X, Y=Y, type=type, data=data, 
    formula=formula, y=y, fitY=fitY, fitZ=fitZ)
  est.nuisance <- stuff$est.nuisance
  nZ <- stuff$nZ
  nY <- stuff$nY
  npsi <- stuff$npsi
  designZ <- stuff$designZ
  designY <- stuff$designY
  designpsi <- stuff$designpsi
  weights <- stuff$weights
  t1 <- stuff$t1
  
  #loop over values of psi and compute sums of estimating functions
  if(is.vector(psi)){
    N <- length(psi)
    U <- vector(length=N)
  }
  if(is.matrix(psi)){
    N <- nrow(psi)
    U <- matrix(nrow=N, ncol=npsi)
  }
  for(i in 1:N){
    if(is.vector(psi))
      psii <- psi[i]
    if(is.matrix(psi))
      psii <- psi[i, ]
    Ui <- estfun(b=c(psii, est.nuisance), Z=Z, X=X, Y=Y, type=type, 
      fitZ=fitZ, fitY=fitY, npsi=npsi, nZ=nZ, nY=nY, 
      designpsi=designpsi, designZ=designZ, designY=designY, 
      weights=weights, data=data, y=y, t1=t1, nuisance=FALSE)
    if(is.vector(psi))
      U[i] <- colSums(Ui)
    if(is.matrix(psi))
      U[i, ] <- colSums(Ui)
  }
  return(U) 
} 

expand <- function(x, names){
  if(is.vector(x))
    x <- x[match(names, names(x))]
  if(is.matrix(x))
    x <- x[match(names, rownames(x)), , drop=FALSE]
  return(x)  
} 

gest <- function(Z, X, Y, type, data, formula=~1, y=NULL, fitY=NULL, fitZ=NULL, 
  clusterid=NULL){
  
  n <- nrow(data) 
  
  #find optimal y if not provided
  if(type=="coxph" & is.null(y)){
    f <- function(y){
      fit <- gest(Z=Z, X=X, Y=Y, type="coxph", formula=formula, y=y, 
        fitY=fitY, fitZ=fitZ, data=data, clusterid=clusterid)
      return(sum(diag(fit$vcov)))
    }
    if(class(fitY)[1]=="survfit"){
      ss <- summary(fitY)
      time <- ss$time
    }
    if(class(fitY)[1]=="coxph"){
      fitY.detail <- coxph.detail(object=fitY)
      time <- fitY.detail$time
    }
    interval <- c(min(time), max(time))
    y <- optimize(f=f, interval=interval)$minimum  
  }
  
  #compute fitZ if not provided
  if(is.null(fitZ)){
    formulaZ <- formula(paste0(Z, "~1"))
    fitZ <- glm(formula=formulaZ, data=data) 
  }
  
  #number of clusters?
  if(!is.null(clusterid))
    ncluster <- length(unique(data[, clusterid]))   
  
  #collect useful stuff  
  stuff <- utilityfun(Z=Z, X=X, Y=Y, type=type, data=data, 
    formula=formula, y=y, fitY=fitY, fitZ=fitZ)
  est.nuisance <- stuff$est.nuisance
  nZ <- stuff$nZ
  nY <- stuff$nY
  npsi <- stuff$npsi
  designZ <- stuff$designZ
  designY <- stuff$designY
  designpsi <- stuff$designpsi
  weights <- stuff$weights 
  t1 <- stuff$t1 
  
  #help function for summing estimating functions
  estfunsums <- function(b, nuisance=FALSE){
    if(length(b)==npsi)
      b <- c(b, est.nuisance)
    return(colSums(estfun(b=b, Z=Z, X=X, Y=Y, type=type, 
      fitZ=fitZ, fitY=fitY, npsi=npsi, nZ=nZ, nY=nY, 
      designpsi=designpsi, designZ=designZ, designY=designY, 
      weights=weights, data=data, y=y, t1=t1, nuisance=nuisance)))
  }
  
  #compute estimate of psi
  fit.nleqslv <- nleqslv(x=c(rep(0, npsi)), fn=estfunsums) 
  est <- fit.nleqslv$x
  names(est) <- paste0(X, ":", colnames(designpsi))
  names(est)[1] <- X
  converged <- fit.nleqslv$termcd==1
 
 #compute variance if solution to estimating equation was found
  if(converged){      
    U <- estfun(b=c(est, est.nuisance), Z=Z, X=X, Y=Y, type=type, 
      fitZ=fitZ, fitY=fitY, npsi=npsi, nZ=nZ, nY=nY, 
      designpsi=designpsi, designZ=designZ, designY=designY, 
      weights=weights, data=data, y=y, t1=t1, nuisance=TRUE) 
    Ipsi <- jacobian(func=estfunsums, x=c(est, est.nuisance))/n
    IZ <- cbind(matrix(0, nrow=nZ, ncol=npsi),
      -solve(summary(object=fitZ)$cov.unscaled)/n,
      matrix(0, nrow=nZ, ncol=nY))
    if(type=="identity" | type=="log")
      IY <- NULL
    if(type=="logit"){
      IY <- cbind(matrix(0, nrow=nY, ncol=npsi+nZ),
        -solve(summary(object=fitY)$cov.unscaled)/n)
    }
    if(type=="coxph"){
      if(class(fitY)[1]=="survfit"){
        IY <- cbind(matrix(0, nrow=nY, ncol=npsi+nZ),
          diag(x=-1, nrow=nY))  
      }
      if(class(fitY)[1]=="coxph"){
        fitY.detail <- coxph.detail(object=fitY)
        E <- expand(fitY.detail$means, data[, Y])
        H0i <- U[, npsi+nZ+nY]
        dH0.dbeta <- as.matrix(E*H0i)
        dH0.dbeta[is.na(dH0.dbeta)] <- 0
        IY <- cbind(matrix(0, nrow=nY, ncol=npsi+nZ),
          rbind(-solve(vcov(object=fitY))/n, -colMeans(dH0.dbeta, na.rm=TRUE)), 
          rbind(matrix(0, nrow=nY-1, ncol=1), -1))
      }
    }
    I <- rbind(Ipsi, IZ, IY)
    if(is.null(clusterid)){
      J <- var(U, na.rm=TRUE)
      vcov <- (solve(I)%*%J%*%t(solve(I))/n)
    }
    else{
      U <- aggr(x=U, clusters=data[, clusterid])
      J <- var(U, na.rm=TRUE)
      vcov <- (solve(I)%*%J%*%t(solve(I))*ncluster/n^2)
    }   
    vcov <- as.matrix(vcov[1:npsi, 1:npsi])
  }
  else{
    U <- NA
    I <- NA
    vcov <- matrix(NA, nrow=npsi, ncol=npsi)  
  }
  rownames(vcov) <- names(est)
  colnames(vcov) <- names(est)
  
  result <- list(est=est, vcov=vcov, estfun=U, d.estfun=I, converged=converged, 
    fitZ=fitZ, y=y)
  
  class(result) <- "gest"

  return(result)

}

ivah <- function(method, Z, X, T, fitZ=NULL, fitX=NULL, fitT=NULL, data,  
  control=FALSE, clusterid=NULL, event, max.time, max.time.psi, n.sim=10){
  
  call <- match.call()
  input <- as.list(environment())
  
  if(method=="ts"){
    result <- tsest(fitX=fitX, fitY=fitT, data=data, control=control, 
      clusterid=clusterid)
  }
  if(method=="g"){
    result <- scs(Z=Z, X=X, time=T, status=event, data=data, fitZ=fitZ, 
      max.time=max.time, max.time.beta=max.time.psi, n.sim=n.sim)
    result$converged <- !is.na(result$est)
    
  }
  if(!result$converged)
    warning("No solution to the estimating equation was found")
  result$call <- call 
  result$input <- input  
  class(result) <- c("ivah", "ivmod")
  return(result)

}

ivbounds <- function(data, Z, X, Y, weights){
  
  zlev <- c(0, 1)
  xlev <- c(0, 1)
  ylev <- c(0, 1) 
  if(is.data.frame(data)){
    if(missing(weights))
      weights <- rep(1, nrow(data))
    incl <- !is.na(data[, Z]) & !is.na(data[, X]) & !is.na(data[, Y])
    data <- data[incl, ]
    weights <- weights[incl]
    if(length(unique(data[, Z]))==3)
      zlev <- c(zlev , 2)
  }
  else{
    if(missing(weights))
      weights <- rep(1, )
    if(length(data)==12)
      zlev <- c(zlev , 2)
  }
  for(y in zlev){
    for(x in xlev){
      for(z in ylev){
        p <- paste0("p", y, x, ".", z)
        if(is.data.frame(data)){
          num <- weighted.mean(x=(data[, Y]==y & data[, X]==x & data[, Z]==z),
            w=weights)
          den <- weighted.mean(x=(data[, Z]==z), w=weights)
          val <- num/den
        }
        else{
          val <- data[p]
        }
        assign(x=p, value=val)
      }
    }
  }
  if(length(zlev)==2){
    p0.low1 <- p10.0+p11.0-p00.1-p11.1
    p0.low2 <- p10.1
    p0.low3 <- p10.0
    p0.low4 <- p01.0+p10.0-p00.1-p01.1
    p0.upp1 <- p01.0+p10.0+p10.1+p11.1
    p0.upp2 <- 1-p00.1
    p0.upp3 <- 1-p00.0
    p0.upp4 <- p10.0+p11.0+p01.1+p10.1
    p0.low <- c(p0.low1, p0.low2, p0.low3, p0.low4)
    p0.upp <- c(p0.upp1, p0.upp2, p0.upp3, p0.upp4) 
    p1.low1 <- p11.0
    p1.low2 <- p11.1
    p1.low3 <- -p00.0-p01.0+p00.1+p11.1
    p1.low4 <- -p01.0-p10.0+p10.1+p11.1
    p1.upp1 <- 1-p01.1
    p1.upp2 <- 1-p01.0
    p1.upp3 <- p00.0+p11.0+p10.1+p11.1
    p1.upp4 <- p10.0+p11.0+p00.1+p11.1
    p1.low <- c(p1.low1, p1.low2, p1.low3, p1.low4)
    p1.upp <- c(p1.upp1, p1.upp2, p1.upp3, p1.upp4)  
  }
  if(length(zlev)==3){
    p0.low1 <- p10.0
    p0.low2 <- p10.1
    p0.low3 <- p10.2
    p0.low4 <- p10.0+p11.0+p10.1+p01.1-1
    p0.low5 <- p10.0+p01.0+p10.1+p11.1-1
    p0.low6 <- p10.1+p11.1+p10.2+p01.2-1
    p0.low7 <- p10.1+p01.1+p10.2+p11.2-1      
    p0.low8 <- p10.2+p11.2+p10.0+p01.0-1
    p0.low9 <- p10.2+p01.2+p10.0+p11.0-1 
    p0.upp1 <- 1-p00.0
    p0.upp2 <- 1-p00.1
    p0.upp3 <- 1-p00.2
    p0.upp4 <- p10.0+p01.0+p10.1+p11.1
    p0.upp5 <- p10.0+p11.0+p10.1+p01.1
    p0.upp6 <- p10.1+p01.1+p10.2+p11.2
    p0.upp7 <- p10.1+p11.1+p10.2+p01.2
    p0.upp8 <- p10.2+p01.2+p10.0+p11.0
    p0.upp9 <- p10.2+p11.2+p10.0+p01.0
    p0.low <- max(p0.low1, p0.low2, p0.low3, p0.low4, p0.low5, p0.low6, p0.low7, 
      p0.low8, p0.low9)
    p0.upp <- min(p0.upp1, p0.upp2, p0.upp3, p0.upp4, p0.upp5, p0.upp6, p0.upp7, 
      p0.upp8, p0.upp9)
    p1.low1 <- p11.0
    p1.low2 <- p11.1
    p1.low3 <- p11.2
    p1.low4 <- p10.0+p11.0-p10.1-p01.1
    p1.low5 <- -p10.0-p01.0+p10.1+p11.1
    p1.low6 <- p10.1+p11.1-p10.2-p01.2
    p1.low7 <- -p10.1-p01.1+p10.2+p11.2
    p1.low8 <- p10.2+p11.2-p10.0 -p01.0
    p1.low9 <- -p10.2-p01.2+p10.0+p11.0
    p1.upp1 <- 1-p01.0
    p1.upp2 <- 1-p01.1
    p1.upp3 <- 1-p01.2
    p1.upp4 <- p10.0+p11.0-p10.1-p01.1+1
    p1.upp5 <- -p10.0-p01.0+p10.1+p11.1+1
    p1.upp6 <- p10.1+p11.1-p10.2-p01.2+1
    p1.upp7 <- -p10.1-p01.1+p10.2+p11.2+1
    p1.upp8 <- p10.2+p11.2-p10.0-p01.0+1
    p1.upp9 <- -p10.2-p01.2+p10.0+p11.0+1
    p1.low <- max(p1.low1, p1.low2, p1.low3, p1.low4, p1.low5, p1.low6, p1.low7, 
      p1.low8, p1.low9)
    p1.upp <- min(p1.upp1, p1.upp2, p1.upp3, p1.upp4, p1.upp5, p1.upp6, p1.upp7, 
      p1.upp8, p1.upp9)
  }
  p0 <- c(max(p0.low), min(p0.upp))
  p1 <- c(max(p1.low), min(p1.upp))  
  names(p0) <- (c("min", "max"))
  names(p1) <- (c("min", "max"))
    
  return(list(p0=p0, p1=p1))

}

ivcoxph <- function(method, Z, X, T, fitZ=NULL, fitX=NULL, fitT, data, 
  formula=~1, control=FALSE, clusterid=NULL, t=NULL){
  
  call <- match.call()
  input <- as.list(environment())
  
  if(method=="ts"){
    result <- tsest(fitX=fitX, fitY=fitT, data=data, control=control, 
      clusterid=clusterid)
  }
  if(method=="g"){
    type <- "coxph"
    result <- gest(Z=Z, X=X, Y=T, type=type, data=data, formula=formula, y=t,
      fitY=fitT, fitZ=fitZ, clusterid=clusterid)
    result$t <- result$y
    result$y <- NULL
  }
  if(!result$converged)
    warning("No solution to the estimating equation was found")
  result$call <- call 
  result$input <- input
  class(result) <- c("ivglm", "ivmod")
  class(result) <- c("ivcoxph", "ivmod")
  return(result)

}

ivglm <- function(method, Z, X, Y, fitZ=NULL, fitX=NULL, fitY=NULL, data, 
  formula=~1, control=FALSE, clusterid=NULL, link){
  
  call <- match.call()
  input <- as.list(environment())
  
  if(method=="ts"){
    result <- tsest(fitX=fitX, fitY=fitY, data=data, control=control, 
      clusterid=clusterid)
  }
  if(method=="g"){
    if(link=="identity")
      type <- "identity"
    if(link=="log")
      type <- "log"
    if(link=="logit")
      type <- "logit"
    result <- gest(Z=Z, X=X, Y=Y, type=type, data=data, formula=formula,
      fitY=fitY, fitZ=fitZ, clusterid=clusterid)
  }
  if(!result$converged)
    warning("No solution to the estimating equation was found")
  result$call <- call 
  result$input <- input
  class(result) <- c("ivglm", "ivmod")
  return(result)

}

plot.ivah <- function (x, gof=FALSE, CI.level=0.95, ...){
  
  dots <- list(...)
  if(gof==TRUE){
    res <- x$GOF.resamp
    ylim <- c(min(c(res[2, ], res[2:22, ])), max(c(res[2, ], res[2:22, ])))
    args <- list(x=res[1, ], y=res[2, ], type="n", ylim=ylim)
    args[names(dots)] <- dots
    if(is.na(match("xlab", names(args))))
      args["xlab"] <- "Time"
    if(is.na(match("ylab", names(args))))
      args["ylab"] <- "Goodness of fit process"
    do.call("plot", args=args)   
    matlines(t(res[1, , drop=FALSE]), t(res[2:20, ]), col="grey", lty="solid")
    lines(res[1, ], res[2, ])
    abline(0, 0)	
  }
  else{
    qqq <- abs(qnorm((1-CI.level)/2))
    B <- x$B
    se <- x$se_B 
    l <- B-qqq*se
    u <- B+qqq*se
    beta <- x$est
    stime <- x$stime
    ylim <- c(min(c(l, beta*stime)), max(c(u, beta*stime)))
    args <- list(x=stime, y=B, type="l", ylim=ylim)
    args[names(dots)] <- dots
    if(is.na(match("xlab", names(args))))
      args["xlab"] <- "Time"
    if(is.na(match("ylab", names(args))))
      args["ylab"] <- "Cumulative regression function"  
    do.call("plot", args=args)
    lines(stime, u, lty="dashed")
    lines(stime, l, lty="dashed")
    abline(0, 0)
    lines(stime, beta*stime)
  }
}


print.ivmod <- function (x, digits=max(3L, getOption("digits")-3L), ...) 
{
    if (length(x$est)) {
        cat("\nCoefficients:\n")
        print.default(format(x$est, digits=digits), print.gap=2, 
            quote=FALSE)
        cat("\n")
    }
    else {
        cat("No coefficients\n\n")
    }
}

print.summary.ivmod <- function(x, digits=max(3L, getOption("digits")-3L), 
  signif.stars=getOption("show.signif.stars"), ...) {
  cat("\nCall:  ", "\n", paste(deparse(x$call), sep="\n", collapse="\n"), 
      "\n", sep="")
  if(!is.null(x$t))
    cat("\nEquation solved at t =", x$t, "\n")
  if(!is.null(x$test0)){
    cat("\nTest for non-significant exposure effect. H_0: B(t)=0 \n")
    cat("   \n")
    prmatrix(signif(x$test0, digits))
    cat("   \n")
    cat("\n")
    cat("Goodness-of-fit test for constant effects model\n")
    prmatrix(signif(x$test_gof, digits))
    cat("   \n");  
    cat("Constant effect model  \n")
  } 
  cat("\nCoefficients:", "\n")
  printCoefmat(x$coefficients, digits=digits, signif.stars=signif.stars, 
    na.print = "NA", ...)
  cat("\n") 
}

scs <- function(Z, X, time, status, data, fitZ=NULL, max.time, max.time.beta, n.sim){
  
  #stuff related to the model for Z
  if(is.null(fitZ)){
    formulaZ <- formula(paste0(Z, "~1"))
    fitZ <- glm(formula=formulaZ, data=data)
  }
  IZ <- summary(object=fitZ)$cov.unscaled
  resZ <- residuals(object=fitZ, type="response")
  designZ <- model.matrix(object=fitZ)
  eps.theta <- (designZ*resZ)%*%IZ  
  g <- family(fitZ)$mu.eta
  dmu.deta <- g(predict(object=fitZ))  
  deta.dbeta <- designZ  
  dmu.dbeta <- dmu.deta*deta.dbeta
  E.dot <- dmu.dbeta
  p.dim <- dim(eps.theta)[2]
  Z.c <- data[, Z]-fitted(object=fitZ)
  
  #estimation of the target parameter
  stime1 <- sort(data[, time])
  n <- length(stime1)
  status_new <- data[, status]
  status_new[data[, time]>max.time] <- 0
  stime <- sort(data[status_new==1, time])
  res <- list()
  
  arvid1 <- data[, time] 
  arvid2 <- data[, X]
  
  res.tmp <- B_est1(arvid1, status_new, stime, stime1, Z.c, arvid2,
    max.time.beta, eps.theta, E.dot, p.dim)
  eps <- res.tmp$eps_B
  k <- length(stime<max.time.beta)
  deps <- eps
 
  deps[2:k,] <- eps[2:k, ]-eps[1:(k-1), ]
  eps.beta <- colSums(deps*res.tmp$at_risk)/res.tmp$tot_risk
  se_beta <- sqrt(sum(eps.beta^2))
  
  chisq_beta <- (res.tmp$beta/se_beta)^2
  pval_beta <- 1-pchisq(chisq_beta, df=1)
  ant.resamp <- n.sim
  GOF.resam0 <- matrix(0, ant.resamp, k)
  max.proc0 <- numeric(ant.resamp)
  GOF.resam <- matrix(0, ant.resamp, k)
  max.proc <- CvM.proc <- numeric(ant.resamp) 
  eps.const.eff <- eps[1:k, ]

  for (j in 1:k)
    eps.const.eff[j, ] <- eps[j,]-stime[j]*eps.beta
  for (j1 in 1:ant.resamp){
    G <- rnorm(n, 0, 1)
    tmp.mat0 <- eps%*%matrix(G, n, 1)
    GOF.resam0[j1,] <- c(tmp.mat0)
    max.proc0[j1] <- max(abs(GOF.resam0[j1, ]))
    tmp.mat <- eps.const.eff%*%matrix(G, n, 1)
    GOF.resam[j1,] <- c(tmp.mat)
    max.proc[j1] <- max(abs(GOF.resam[j1, ]))
    CvM.proc[j1] <- sum(GOF.resam[j1, ]^2*c(stime[2:k]-stime[1:(k-1)], 
      max.time.beta-stime[k]))
  }
  GOF.proc0 <- res.tmp$B[1:k]
  max.obs0 <- max(abs(GOF.proc0))
  GOF.proc <- res.tmp$B[1:k]-res.tmp$beta*stime
  max.obs <- max(abs(GOF.proc))
  CvM.obs <- sum(GOF.proc^2*c(stime[2:k]-stime[1:(k-1)],max.time.beta-stime[k]))
  pval_0 <- sum(max.proc0>max.obs0)/ant.resamp
  pval.sup <- sum(max.proc>max.obs)/ant.resamp
  pval.CvM <- sum(CvM.proc>CvM.obs)/ant.resamp
  res$stime <- res.tmp$stime
  res$B <- res.tmp$B
  res$se_B <- res.tmp$se
  res$pval_0 <- pval_0
  res$eps_B <- res.tmp$eps_B
  est <- res.tmp$beta
  names(est) <- X
  res$est <- est
  vcov <- matrix(se_beta^2)
  rownames(vcov) <- X
  colnames(vcov) <- X
  res$vcov <- vcov
  res$pval_psi <- pval_beta
  res$pval_GOF_sup <- pval.sup
  res$pval_GOF_CvM <- pval.CvM
  res$fitZ <- fitZ
  if (n.sim>50)
    res$GOF.resamp <- rbind(stime[1:k], GOF.proc, GOF.resam[1:50,])
  return(res)

}


summary.ivmod <- function(object, digits=max(3L, getOption("digits")-3L), ...) {
  s.err <- sqrt(diag(as.matrix(object$vcov)))
  zvalue <- object$est/s.err
  pvalue <- 2*pnorm(-abs(zvalue))
  coef.table <- as.matrix(cbind(object$est, s.err, zvalue, 
        pvalue))
  dimnames(coef.table) <- list(names(object$est), c("Estimate", 
      "Std. Error", "z value", "Pr(>|z|)"))
  ans <- list(call=object$call, coefficients=coef.table, t=object$t)
  if(class(object)[1]=="ivah" & object$input$method=="g"){
    test0 <- cbind(object$pval_0) 
    colnames(test0)  <- c("Supremum-test pval")
    rownames(test0)<- c(object$input$X) 
    test_gof <- cbind(object$pval_GOF_sup)
    colnames(test_gof) <- c("Supremum-test pval")
    rownames(test_gof) <- c("        ")
    ans$test0 <- test0
    ans$test_gof <- test_gof
  }
  class(ans) <- "summary.ivmod"
  return(ans)
}



tsest <- function(fitX, fitY, data, control=FALSE, clusterid=NULL){
  
  #preliminaries
  n <- nrow(data)
  weights <- expand(fitX$prior.weights, rownames(data))
  if(!is.null(clusterid))
    ncluster <- length(unique(data[, clusterid]))
  
  #collect features of fitX
  X <- as.character(fitX$formula[2])
  resX <- expand(residuals(object=fitX, type="response"), rownames(data))
  designX <- expand(model.matrix(object=fitX), rownames(data))
  nX <- length(fitX$coef)
   
  #estimate
  Xhat <- expand(predict(object=fitX, type="response"), rownames(data))
  data.Xhat <- data
  data.Xhat[, X] <- Xhat
  call <- fitY$call
  frml <- fitY$formula
  if(control){
    data.Xhat[, "R"] <- resX
    call$formula <- update(frml, .~.+R)
  }
  call$data <- data.Xhat 
  fitY <- eval(call, envir=environment(frml))
  est <- fitY$coef 
  
  #collect features of fitY
  if(class(fitY)[1]=="glm"){
    resY <- expand(residuals(object=fitY, type="response"), rownames(data))
    designY <- expand(model.matrix(object=fitY), rownames(data))
  }
  if(class(fitY)[1]=="coxph")
    resY <- expand(residuals(object=fitY, type="score"), rownames(data))
  if(class(fitY)[1]=="ah"){
    resY <- predict(object=fitY, type="residuals")
    rownames(resY) <- fitY$incl
    colnames(resY) <- names(fitY$coefficients)
    resY <- expand(resY, rownames(data))
  }
  nY <- length(fitY$coef)
  
  #variance 
  UX <- weights*resX*designX
  UX[is.na(UX)] <- 0
  if(class(fitY)[1]=="glm")
    UY <- weights*resY*designY
  if(class(fitY)[1]=="coxph")
    UY <- weights*resY  
  #for an ah objects the residuals are weighted
  if(class(fitY)[1]=="ah")
    UY <- resY
  UY[is.na(UY)] <- 0
  U <- cbind(UX, UY)
  if(!is.null(clusterid))
      U <- aggr(x=U, clusters=data[, clusterid])
  J <- var(U)
  IX <- cbind(-solve(summary(object=fitX)$cov.unscaled)/n,
    matrix(0, nrow=nX, ncol=nY))    
  UYfunc <- function(b){
    Xhat <- as.vector(family(fitX)$linkinv(designX%*%b)) 
    data.Xhat[, X]  <- Xhat
    if(control)
      data.Xhat[, "R"] <- data[, X]-Xhat
    if(class(fitY)[1]=="glm"){
      designY <- expand(model.matrix(object=fitY$formula, data=data.Xhat), 
        rownames(data))
      Yhat <- as.vector(family(fitY)$linkinv(designY%*%est))
      Y <- expand(fitY$y, rownames(data))
      resY <- Y-Yhat
      UY <- weights*resY*designY
    }
    if(class(fitY)[1]=="coxph"){
      fitY$call$data <- data.Xhat
      resY <- expand(residuals(object=fitY, type="score"), rownames(data))
      UY <- as.matrix(weights*resY)
    }
    if(class(fitY)[1]=="ah"){
      fitY$data$X <- model.matrix(object=fitY$formula, 
        data=data.Xhat)[, -1, drop=FALSE] 
      resY <- predict(object=fitY, type="residuals")
      rownames(resY) <- fitY$incl
      colnames(resY) <- names(fitY$coefficients)
      resY <- expand(resY, rownames(data))
      UY <- resY
    }
    UY[is.na(UY)] <- 0  
    colMeans(UY)
  } 
  if(class(fitY)[1]=="glm")
    IY <- cbind(jacobian(func=UYfunc, x=fitX$coef),
      -solve(summary(object=fitY)$cov.unscaled)/n)
  if(class(fitY)[1]=="coxph")
    IY <- cbind(jacobian(func=UYfunc, x=fitX$coef),
      -solve(vcov(object=fitY))/n)   
  if(class(fitY)[1]=="ah")
    IY <- cbind(jacobian(func=UYfunc, x=fitX$coef),
      -fitY$D/n)
  I <- rbind(IX, IY)
  if(is.null(clusterid))
    vcov <- (solve(I)%*%J%*%t(solve(I))/n)
  else
    vcov <- (solve(I)%*%J%*%t(solve(I))*ncluster/n^2)
  vcov <- vcov[(nX+1):(nX+nY), (nX+1):(nX+nY), drop=FALSE]
  rownames(vcov) <- names(est)
  colnames(vcov) <- names(est)
  
  if(class(fitY)[1]=="glm"){
    converged <- fitY$converged
  }
  else{
    converged <- TRUE
  }
  result <- list(est=est, vcov=vcov, estfun=U, d.estfun=I, fitY=fitY, 
    converged=converged)
  class(result) <- "tsest"

  return(result)
  
}

#extracts and computes various useful stuff for G-estimation  
utilityfun <- function(Z, X, Y, type, data, formula, y, fitY, fitZ){
  
  n <- nrow(data)
  
  #stuff related to Z 
  nZ <- length(fitZ$coef)
  designZ <- expand(model.matrix(object=fitZ), rownames(data)) 
  weights <- expand(fitZ$prior.weights, rownames(data))
  est.nuisance <- fitZ$coef
  
  #stuff related to Y 
  t1 <- NULL  
  if(type=="identity" | type=="log"){
    nY <- 0  
    designY <- NULL
  }
  if(type=="logit"){
    nY <- length(fitY$coef) 
    designY <- expand(model.matrix(object=fitY), rownames(data))
    est.nuisance <- c(est.nuisance, fitY$coef)
  }
  if(type=="coxph"){
    #left-truncation?    
    if(type=="coxph"){   
      temp <- all.vars(fitY$call$formula[[2]])
      if(length(temp)==3) 
        t1 <- temp[1]  
    }
    if(class(fitY)[1]=="survfit"){
      designY <- NULL
      ss <- summary(fitY)
      strata <- ss$strata
      n.strata <- summary(strata)
      nY <- length(n.strata)
      strata.names <- names(n.strata)
      time <- ss$time
      nevent <- ss$n.event
      nrisk <- ss$n.risk  
      dH <- nevent/nrisk
      H <- vector(length=nY)
      names(H) <- strata.names
      breaks <- c(0, cumsum(n.strata))
      for(k in 1:nY){
        incl <- (breaks[k]+1):breaks[k+1] 
        Hfun <- stepfun(time[incl], c(0, cumsum(dH[incl])))
        H[k] <- Hfun(y) 
      }
      est.nuisance <- c(est.nuisance, fitY$coef, H)
    }
    if(class(fitY)[1]=="coxph"){
      nY <- length(fitY$coef)+1 
      designY <- expand(model.matrix(object=fitY), rownames(data))
      fitY.detail <- coxph.detail(object=fitY)
      time <- fitY.detail$time
      nevent <- fitY.detail$nevent
      nrisk <- fitY.detail$nrisk
      dH0 <- fitY.detail$hazard
      names(dH0) <- time
      H0fun <- stepfun(time, c(0, cumsum(dH0)))
      H0 <- H0fun(y)  
      est.nuisance <- c(est.nuisance, fitY$coef, H0)       
    }   
  }
  
  #stuff related to psi 
  temp <- model.matrix(object=formula, data=data)
  #If formula==~1, then model.matrix does not use the row names in data!
  #Note: cannot remove if(formula==~1), since rownames(temp) <- rownames(data)
  #does not work if missing, since then nrow(temp)!=nrow(data). However,
  #if formula==~1, then missing will not reduce size of temp. 
  if(formula==~1)
    rownames(temp) <- rownames(data)
  designpsi <- expand(temp, rownames(data))
  npsi <- ncol(designpsi)   
  
  return(list(est.nuisance=est.nuisance, npsi=npsi, nZ=nZ, nY=nY, 
    designpsi=designpsi, designZ=designZ, designY=designY, weights=weights,
    t1=t1))

}






