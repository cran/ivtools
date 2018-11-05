\name{ivglm}

\alias{ivglm}

\title{
Instrumental variable estimation of the causal exposure effect in 
generalized linear models 
}

\description{
\code{ivglm} performs instrumental variable estimation of the causal exposure effect in 
generalized linear models with individual-level data. Below, \eqn{Z}, \eqn{X}, and 
\eqn{Y} are the instrument, the exposure, and the outcome, respectively. 
\eqn{L} is a vector of covariates that we wish to control for in the analysis; 
these would typically be confounders for the instrument and the outcome.
}     

\usage{
ivglm(method, Z, X, Y, fitZ=NULL, fitX=NULL, fitY=NULL, data, 
  formula=~1, control=FALSE, clusterid=NULL, link)
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
  \item{Y}{
a string specifying the name of the outcome \eqn{Y} in \code{data}. This argument
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
 \item{fitY}{
an object of class \code{"glm"}, as returned by the \code{glm} function 
  in the \code{stats} package. This is a fitted GLM for \eqn{E(Y|L,Z,X)}. 
This argument is not used when \code{method="g"} and \code{link="identity"} or 
\code{link="log"}.  
} 
  \item{data}{
a data frame containing the variables in the model. The covariates, instrument,
exposure and outcome can have arbitrary names, e.g. they don't need to 
be called \code{L}, \code{Z}, \code{X} and \code{Y}.
}  
  \item{formula}{
  an object of class \code{"formula"}, with no left-hand side. This specifies
the causal interaction terms \eqn{m(L)}; see `Details'. Defaults to \code{~1}, i.e. 
main effect only. This argument is not used when \code{method="ts"}.  
}
  \item{control}{
should the control function \eqn{R=X-\hat{X}} be used when re-fitting 
\code{fitY}? This argument is not used when \code{method="g"}.   
}
  \item{clusterid}{
an optional string containing the name of a cluster identification variable when 
data are clustered. Specifying \code{clusterid} corrects the standard errors
but does not affect the estimates. 
}
 \item{link}{
 a string specifying the link function for the causal generalized linear model;
 see `Details'. Either \code{"identity"}, \code{"log"}, or \code{"logit"}. 
  
}

}

\details{ 
\code{ivglm} estimates the parameter \eqn{\psi} in the causal generalized linear model
\deqn{\eta\{E(Y|L,Z,X)\}-\eta\{E(Y_0|L,Z,X)\}=m^T(L)X\psi.}
Here, \eqn{E(Y_0|L,Z,X)} is counterfactual mean of the outcome, 
had the exposure been set to 0. The link function
 \eqn{\eta} is either the identity, log or logit link, as specified by 
 the \code{link} argument. The vector function \eqn{m(L)} contains interaction terms
 between \eqn{L} and \eqn{X}. If \code{method="ts"}, then these are specified 
 implicitly through the model \code{fitY}. If \code{method="g"}, then these     
 are specified explicitly through the \code{formula} argument.
 
If \code{method="ts"}, then two-stage estimation of \eqn{\psi} is performed.
In this case, the model \code{fitX} is used to construct predictions
\eqn{\hat{X}=\hat{E}(X|L,Z)}. These predictions are subsequently used to re-fit 
the model \code{fitY}, with \eqn{X} replaced with \eqn{\hat{X}}. The obtained 
coefficient(s) for \eqn{X} is the two-stage estimator \eqn{\hat{\psi}}. 

If \code{method="g"}, then G-estimation of \eqn{\psi} is performed. In this case,
the estimator is obtained as the solution to the estimating equation
\deqn{\sum_{i=1}^nm(L_i)\{Z_i-\hat{E}(Z|L_i)\}h_i(\psi)=0.}
In this equation, \eqn{\hat{E}(Z|L_i)} is an estimate of \eqn{E(Z|L_i)}
obtained from the model \code{fitZ}. In the absence of \eqn{L}, \eqn{E(Z|L_i)} reduces to 
\eqn{E(Z)}, which is estimated as \eqn{\sum_{i=1}^nZ_i/n}. In this case, 
\code{fitZ} may be omitted. The function \eqn{h_i(\psi)} is defined as
\deqn{h_i(\psi)=Y_i-m^T(L_i)\psi X_i}
when \code{link="identity"},
\deqn{h_i(\psi)=Y_i exp\{-m^T(L_i)\psi X_i\}}
when \code{link="log"}, and
\deqn{h_i(\psi)=expit\{\hat{E}(Y|L_i,Z_i,X_i)-m^T(L_i)\psi X_i\}}
when \code{link="logit"}. In the latter, \eqn{\hat{E}(Y|L_i,Z_i,X_i)} is
an estimate of \eqn{E(Y|L_i,Z_i,X_i)} obtained from the model \code{fitY}. 
}

\value{
\code{"ivglm"} returns an object of class \code{"ivglm"}, which inherits from 
class \code{"ivmod"}. An object of class \code{"ivglm"} is a list containing 
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
\item{estfun}{
  a matrix of all estimating functions used in the estimation process.
One row for each subject, one column for each parameter. If \code{method="ts"},
then the first columns correspond to the parameters estimated by \code{fitX}, and
the last columns correspond to the parameters estimated by the re-fitted model 
\code{fitY}. If \code{method="g"}, then the first columns correspond to \eqn{\psi}, 
and the remaining columns correspond to the parameters estimated by \code{fitZ} and 
(if \code{link="logit"}) \code{fitY}.    
  }
\item{d.estfun}{
  the jacobian matrix of \code{colSums(estfun)}.    
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

}

\references{
Bowden J., Vansteelandt S. (2011). Mendelian randomization analysis of
case-control data using structural mean models. \emph{Statistics in Medicine}
\bold{30}(6), 678-694.
 
Vansteelandt S., Bowden J., Babanezhad M., Goetghebeur E. (2011). 
On instrumental variables estimation of causal odds ratios.
\emph{Statistical Science} \bold{26}(3), 403-422.

}

\author{
Arvid Sjolander. 
}

\note{
\code{ivglm} allows for weights. However, these are defined implicitly 
through the input models. Thus, when models are used as input to \code{ivglm}, 
these models have to be fitted with the same weights. When \code{method="g"}
the weights are taken from \code{fitZ}, so this must be specified.    
}

\examples{

set.seed(9)

##Note: the parameter values in the examples below are chosen to make 
##Y0 independent of Z, which is necessary for Z to be a valid instrument.

n <- 1000
psi0 <- 0.5
psi1 <- 0.2

##---Example 1: linear model and interaction between X and L---

L <- rnorm(n)
Z <- rnorm(n, mean=L)
X <- rnorm(n, mean=Z)
m0 <- X-Z+L 
Y <- rnorm(n, mean=psi0*X+psi1*X*L+m0)
data <- data.frame(L, Z, X, Y)

#two-stage estimation
fitX <- glm(formula=X~Z, data=data)
fitY <- glm(formula=Y~X+L+X*L, data=data)
fitIV <- ivglm(method="ts", fitX=fitX, fitY=fitY, data=data, control=TRUE) 
summary(fitIV)

#G-estimation
fitZ <- glm(formula=Z~L, data=data)
fitIV <- ivglm(method="g", Z="Z", X="X", Y="Y", fitZ=fitZ, data=data, 
  formula=~L, link="identity")
summary(fitIV)

##---Example 2: logistic model and no covariates--- 

Z <- rbinom(n, 1, 0.5)
X <- rbinom(n, 1, 0.7*Z+0.2*(1-Z)) 
m0 <- plogis(1+0.8*X-0.39*Z)
Y <- rbinom(n, 1, plogis(psi0*X+log(m0/(1-m0)))) 
data <- data.frame(Z, X, Y)

#two-stage estimation
fitX <- glm(formula=X~Z, family="binomial", data=data)
fitY <- glm(formula=Y~X, family="binomial", data=data)
fitIV <- ivglm(method="ts", fitX=fitX, fitY=fitY, data=data, control=TRUE) 
summary(fitIV)

#G-estimation
fitY <- glm(formula=Y~X+Z+X*Z, family="binomial", data=data)
fitIV <- ivglm(method="g", Z="Z", X="X", Y="Y", fitY=fitY, data=data, link="logit")
summary(fitIV)


}
