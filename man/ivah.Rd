\name{ivah}

\alias{ivah}

\title{
Instrumental variable estimation of the causal exposure effect in 
additive hazards (AH) models 
}

\description{
\code{ivah} performs instrumental variable estimation of the causal exposure effect in 
AH models with individual-level data. Below, \eqn{Z}, \eqn{X}, and 
\eqn{T} are the instrument, the exposure, and the outcome, respectively. 
\eqn{L} is a vector of covariates that we wish to control for in the analysis; 
these would typically be confounders for the instrument and the outcome.
} 

\usage{
ivah(method, Z, X, T, fitZ=NULL, fitX=NULL, fitT=NULL, data,  
  control=FALSE, clusterid=NULL, event, max.time, max.time.psi, n.sim=10)
}

\arguments{
\item{method}{
a string specifying the desired estimation method; either \code{"ts"} for two-stage
estimation, or \code{"g"} for G-estimation. 
}
\item{Z}{
a string specifying the name of the instrument \eqn{Z} in \code{data}. This argument
is not used when \code{method="ts"}. 
}
  \item{X}{
a string specifying the name of the exposure \eqn{X} in \code{data}. This argument
is not used when \code{method="ts"}.
}
  \item{T}{
a string specifying the name of the follow-up time \eqn{T} in \code{data}. This argument
is not used when \code{method="ts"}.
}
  \item{fitZ}{
an object of class \code{"glm"}, as returned by the \code{glm} function 
in the \code{stats} package. This is a fitted GLM for \eqn{E(Z|L)}. This argument
is not used when \code{method="ts"}. It is not required when \code{method="g"}
and covariates are absent. 
}
\item{fitX}{
an object of class \code{"glm"}, as returned by the \code{glm} function 
  in the \code{stats} package. This is a fitted GLM for \eqn{E(X|L,Z)}. This argument
is not used when \code{method="g"}. 
}
 \item{fitT}{
If \code{method="ts"}, then this is an object of class \code{"ah"}, as 
  returned by the \code{ah} function in the \code{ivtools} package. 
  In this case it is a fitted AH model for \eqn{\lambda(t|L,X)}. 
  This argument is not used when \code{method="g"}.  
} 
  \item{data}{
a data frame containing the variables in the model. The covariates, instrument,
exposure and outcome can have arbitrary names, e.g. they don't need to 
be called \code{L}, \code{Z}, \code{X} and \code{T}.
}  
  \item{control}{
should the control function \eqn{R=X-\hat{X}} be used when re-fitting 
\code{fitY}? This argument is not used when \code{method="g"}.   
}
  \item{clusterid}{
an optional string containing the name of a cluster identification variable when 
data are clustered. Specifying \code{clusterid} corrects the standard errors
but does not affect the estimates. This argument is not used when 
\code{method="g"}, since correction for clustered data is currently not implemented
for G-estimation. 
}
  \item{event}{
a string specifying the name of the status indicator, 0="no event", 1="event".
This argument is not used when \code{method="ts"}. 
}

  \item{max.time}{
follow-up for estimating \eqn{B(t)} with G-estimation.
This argument is not used when \code{method="ts"}. 
}
  \item{max.time.psi}{
forllow-up for estimating \eqn{\psi} with G-estimation. 
This argument is not used when \code{method="ts"}.
}
  \item{n.sim}{
number of resamplings for testing goodness-of-fit of constant effects model
for G-estimation. This argument is not used when \code{method="ts"}.  
}

}

\details{ 
The \code{ivah} estimates different parameters, depending on whether
\code{method="ts"} or \code{method="g"}. If \code{method="ts"}, then 
\code{ivah} uses two-stage estimation to estimate the parameter \eqn{\psi} in the causal AH model
\deqn{\lambda(t|L,Z,X)-\lambda_0(t|L,Z,X)=m^T(L)X\psi.}
Here, \eqn{\lambda_0(t|L,Z,X)} is counterfactual hazard function,
had the exposure been set to 0. The vector function \eqn{m(L)} contains interaction terms
 between \eqn{L} and \eqn{X}. These are specified 
 implicitly through the model \code{fitY}. The model \code{fitX} is used to 
 construct predictions \eqn{\hat{X}=\hat{E}(X|L,Z)}. These predictions are 
 subsequently used to re-fit the model \code{fitY}, with \eqn{X} replaced with 
 \eqn{\hat{X}}. The obtained coefficient(s) for \eqn{X} is the two-stage 
 estimator \eqn{\hat{\psi}}.  
 
If \code{method="g"}, then \code{ivah} uses G-estimation to estimate the function 
\eqn{B(t)} in the causal AH model
\deqn{\lambda(t|L,Z,X)-\lambda_0(t|L,Z,X)=dB(t).} 
It also delivers an estimate of \eqn{dB(t)} assuming that this function is 
constant across time (=\eqn{\psi}).
}

\value{
\code{"ivah"} returns an object of class \code{"ivah"}, which inherits from 
class \code{"ivmod"}. An object of class \code{"ivah"} is a list containing 
\item{call}{
  the matched call. 
  }
\item{input}{
  \code{input} is a list containing all input arguments     
  }
\item{est}{
  a vector containing the estimate of \eqn{\psi}.  
  }
\item{vcov}{
  the variance-covariance matrix for the estimate of \eqn{\psi}, 
obtained with the sandwich formula. 
  }
\item{converged}{
  logical. Was a solution found to the estimating equations?   
}
\item{fitZ}{
  the model \code{fitZ} used in the estimation process when \code{method="g"}.
  This element is NULL when \code{method="ts"}. 
}
\item{fitY}{
  the re-fitted model \code{fitY} used in the estimation process when \code{method="ts"}.
  This element is NULL when \code{method="g"}.  
}
\item{stime}{
  the ordered event times within (0,max.time). This element is NULL when \code{method="ts"}. 
}
\item{B}{
  the estimate of \eqn{B(t)}. This element is NULL when \code{method="ts"}.   
}
\item{se_B}{
  the standard error of the estimate of \eqn{B(t)}. This element is NULL when \code{method="ts"}.
}
\item{pval_0}{
  p-value corresponding to supremum test of the null \eqn{B(t)=0}. 
  This element is NULL when \code{method="ts"}.
}
\item{eps_B}{
  the iid-decomposition of \eqn{\sqrt{n}(\hat{B}(t) - B(t))}. 
  This element is NULL when \code{method="ts"}.
}
\item{pval_psi}{
  p-value corresponding to the null \eqn{\psi=0}. 
  This element is NULL when \code{method="ts"}.
}
\item{pval_GOF_sup}{
  p-value corresponding to supremum test of the null \eqn{B(t)=\psi}.  
  This element is NULL when \code{method="ts"}.
}
\item{pval_GOF_CvM}{
  as pval_GOF_sup but now based on the Cramer Von Mises test statistic.  
  This element is NULL when \code{method="ts"}.
}
\item{GOF.resamp}{
  a matrix with first row the ordered jump times in (0,max.time.bet),
 second row the observed test process, and the remaining rows are 
 50 processes sampled under the null. 
  This element is NULL when \code{method="ts"}.
}
}

\references{

Martinussen T., Vansteelandt S., Tchetgen Tchetgen E.J., Zucker D.M. (2017). 
Instrumental variables estimation of exposure effects on a time-to-event 
endpoint using structural cumulative survival models. 
\emph{Epidemiology} \bold{73}(4): 1140-1149.

Tchetgen Tchetgen E.J., Walter S., Vansteelandt S., Martinussen T., Glymour M. (2015).
Instrumental variable estimation in a survival context. \emph{Epidemiology} \bold{26}(3): 402-410. 

}

\author{
Arvid Sjolander and Torben Martinussen. 
}

\note{
\code{ivah} allows for weights. However, these are defined implicitly 
through the input models. Thus, when models are used as input to \code{ivah}, 
these models have to be fitted with the same weights.

Left-truncation and correction of standard errors for clustered data are currerntly not
implemented when \code{method="g"}.     
}

\examples{

require(ahaz)

set.seed(9)

n <- 1000
psi0 <- 0.2
psi1 <- 0.0

U <- runif(n)
L <- runif(n)
Z <- rbinom(n, 1, plogis(-0.5+L)) 
X <- runif(n, min=Z+U, max=2+Z+U)
T <- rexp(n, rate=psi0*X+psi1*X*L+0.2*U+0.2*L)
C <- 5  #administrative censoring at t=5
d <- as.numeric(T<C)
T <- pmin(T, C) 
data <- data.frame(L, Z, X, T, d)
#break ties
data$T <- data$T+rnorm(n=nrow(data), sd=0.001)

#two-stage estimation
fitX <- glm(formula=X~Z+L, data=data)
fitT <- ah(formula=Surv(T, d)~X+L+X*L, data=data)
fitIV <- ivah(method="ts", fitX=fitX, fitT=fitT, data=data, control=TRUE)
summary(fitIV)

#G-estimation
fitZ <- glm(formula=Z~L, family="binomial", data=data)
fitIV <- ivah(method="g", Z="Z", X="X", T="T", fitZ=fitZ, data=data,  
          event="d", max.time=4, max.time.psi=4, n.sim=100)
summary(fitIV)
plot(fitIV)



}
