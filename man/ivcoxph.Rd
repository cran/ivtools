\name{ivcoxph}

\alias{ivcoxph}

\title{
Instrumental variable estimation of the causal exposure effect in 
Cox proportional hazards (PH) models 
}

\description{
\code{ivcoxph} performs instrumental variable estimation of the causal exposure effect in 
Cox PH models with individual-level data. Below, \eqn{Z}, \eqn{X}, and 
\eqn{T} are the instrument, the exposure, and the outcome, respectively. 
\eqn{L} is a vector of covariates that we wish to control for in the analysis; 
these would typically be confounders for the instrument and the outcome.
} 

\usage{
ivcoxph(estmethod, Z, X, T, fitZ=NULL, fitX=NULL, fitT, data, 
  formula=~1, ctrl=FALSE, clusterid=NULL, t=NULL, ...)
}

\arguments{
\item{estmethod}{
a string specifying the desired estimation method; either \code{"ts"} for two-stage
estimation, or \code{"g"} for G-estimation. 
}
\item{Z}{
a string specifying the name of the instrument \eqn{Z} in \code{data}. This argument
is not used when \code{estmethod="ts"}. 
}
  \item{X}{
a string specifying the name of the exposure \eqn{X} in \code{data}. This argument
is not used when \code{estmethod="ts"}.
}
  \item{T}{
a string specifying the name of the follow-up time \eqn{T} in \code{data}. This argument
is not used when \code{estmethod="ts"}.
}
  \item{fitZ}{
an object of class \code{"glm"}, as returned by the \code{glm} function 
in the \code{stats} package. This is a fitted GLM for \eqn{E(Z|L)}. This argument
is not used when \code{estmethod="ts"}. It is not required when \code{estmethod="g"}
and covariates are absent. 
}
\item{fitX}{
an object of class \code{"glm"}, as returned by the \code{glm} function 
  in the \code{stats} package. This is a fitted GLM for \eqn{E(X|L,Z)}. This argument
is not used when \code{estmethod="g"}. 
}
 \item{fitT}{
If \code{estmethod="ts"}, then this is an object of class \code{"coxph"}, as 
  returned by the \code{coxph} function in the \code{survival} package. 
  In this case it is a fitted Cox PH model for \eqn{\lambda(t|L,X)}. 
  If \code{estmethod="g"}, then this is either an object of class \code{"coxph"} 
  or an object of class \code{"survfit"}, as returned by the \code{coxph} function 
  in the \code{survival} package. In this case it is a fitted Cox PH model for 
  \eqn{\lambda(t|L,Z,X)} or a non-parametric model for \eqn{S(t|L,Z,X)},
  respectively.  
} 
  \item{data}{
a data frame containing the variables in the model. The covariates, instrument,
exposure and outcome can have arbitrary names, e.g. they don't need to 
be called \code{L}, \code{Z}, \code{X} and \code{T}.
}  
  \item{formula}{
  an object of class \code{"formula"}, with no left-hand side. This specifies
the causal interaction terms \eqn{m(L)}; see `Details'. Defaults to \code{~1}, i.e. 
main effect only. This argument is not used when \code{estmethod="ts"}.  
}
  \item{ctrl}{
logical. Should the control function \eqn{R=X-\hat{X}} be used when re-fitting 
\code{fitY}? This argument is not used when \code{estmethod="g"}.   
}
  \item{clusterid}{
an optional string containing the name of a cluster identification variable when 
data are clustered. Specifying \code{clusterid} corrects the standard errors
but does not affect the estimates. 
}
 \item{t}{
 a numeric scalar specifying the time point at which to solve the estimating 
equation when \code{estmethod="g"}; see `Details'. This argument is not used when
\code{estmethod="ts"}. If not supplied, then the estimating equation is solved 
at the optimal value of \code{t}, defined as the value that 
minimizes \eqn{trace\{var(\hat{\psi})\}}; see Martinussen et al (2017).
  }
  \item{...}{
  optional arguments passed on to the \code{nleqslv} function, which is used to 
  solve the estimating equations when \code{estmethod="g"}. See the help pages 
  for \code{nleqslv}. This argument is not used when \code{estmethod="ts"}. 
  } 

}

\details{ 
\code{ivcoxph} estimates the parameter \eqn{\psi} in the causal Cox PH model
\deqn{\textrm{log}\{\lambda(t|L,Z,X)\}-\textrm{log}\{\lambda_0(t|L,Z,X)\}=m^T(L)X\psi.}
Here, \eqn{\lambda_0(t|L,Z,X)} is counterfactual hazard function,
had the exposure been set to 0. The vector function \eqn{m(L)} contains interaction terms
 between \eqn{L} and \eqn{X}. If \code{estmethod="ts"}, then these are specified 
 implicitly through the model \code{fitY}. If \code{estmethod="g"}, then these     
 are specified explicitly through the \code{formula} argument.
 
If \code{estmethod="ts"}, then two-stage estimation of \eqn{\psi} is performed.
In this case, the model \code{fitX} is used to construct predictions
\eqn{\hat{X}=\hat{E}(X|L,Z)}. These predictions are subsequently used to re-fit 
the model \code{fitY}, with \eqn{X} replaced with \eqn{\hat{X}}. The obtained 
coefficient(s) for \eqn{X} is the two-stage estimator \eqn{\hat{\psi}}. 

If \code{estmethod="g"}, then G-estimation of \eqn{\psi} is performed. In this case,
the estimator is obtained as the solution to the estimating equation
\deqn{H(\psi)=\sum_{i=1}^nm(L_i)\{Z_i-\hat{E}(Z|L_i)\}h_i(\psi;t)=0,}
where
\deqn{h_i(\psi;t)=\hat{S}(t|L_i,Z_i,X_i)^{\textrm{exp}\{-m^T(L_i)\psi X_i\}}.}
The equation is solved at the value of \eqn{t} specified by the argument \code{t}.
\eqn{\hat{S}(t|L_i,Z_i,X_i)} is an estimate of \eqn{S(t|L_i,Z_i,X_i)} obtained 
from the model \code{fitY}. 
 
}

\value{
\code{ivcoxph} returns an object of class \code{"ivcoxph"}, which inherits from 
class \code{"ivmod"}. An object of class \code{"ivcoxph"} is a list containing 
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
\item{estfunall}{
  a matrix of all subject-specific contributions to the estimating functions used in the estimation process.
One row for each subject, one column for each parameter. If \code{estmethod="ts"},
then the first columns correspond to the parameters estimated by \code{fitX}, and
the last columns correspond to the parameters estimated by the re-fitted model 
\code{fitY}. If \code{estmethod="g"}, then the first columns correspond to \eqn{\psi}, 
and the remaining columns correspond to the parameters estimated by \code{fitZ} and 
\code{fitY}.    
  }
\item{d.estfun}{
  the jacobian matrix of \code{colSums(estfun)}.    
  }
\item{converged}{
  logical. Was a solution found to the estimating equations?   
}
\item{fitZ}{
  the model \code{fitZ} used in the estimation process when \code{estmethod="g"}.
  This element is NULL when \code{estmethod="ts"}. 
}
\item{fitY}{
  the re-fitted model \code{fitY} used in the estimation process when \code{estmethod="ts"}.
  This element is NULL when \code{estmethod="g"}.  
}
\item{t}{
  the value of \code{t} used in the estimation process. This element is NULL 
  when \code{estmethod="ts"}. 
}

}

\references{

Martinussen T., Sorensen D.D., Vansteelandt S. (2017). 
Instrumental variables estimation under a structural Cox model.
\emph{Biostatistics} <doi:10.1093/biostatistics/kxx057>.

Tchetgen Tchetgen E.J., Walter S., Vansteelandt S., Martinussen T., Glymour M. (2015).
Instrumental variable estimation in a survival context. \emph{Epidemiology} \bold{26}(3): 402-410. 

}

\author{
Arvid Sjolander. 
}

\note{
\code{ivglm} allows for weights. However, these are defined implicitly 
through the input models. Thus, when models are used as input to \code{ivglm}, 
these models have to be fitted with the same weights. When \code{estmethod="g"}
the weights are taken from \code{fitZ}, so this must be specified.   
}

\examples{

require(survival)

set.seed(9)

##Note: the parameter values in the examples below are chosen to make 
##Y0 independent of Z, which is necessary for Z to be a valid instrument.

n <- 10000
psi0 <- 0.5
Z <- rbinom(n, 1, 0.5)
X <- rbinom(n, 1, 0.7*Z+0.2*(1-Z))
m0 <- exp(0.8*X-0.41*Z) #T0 independent of Z at t=1
T <- rexp(n, rate=exp(psi0*X+log(m0)))
C <- rexp(n, rate=exp(psi0*X+log(m0))) #50% censoring
d <- as.numeric(T<C)
T <- pmin(T, C)
data <- data.frame(Z, X, T, d)

#two-stage estimation
fitX <- glm(formula=X~Z, data=data)
fitT <- coxph(formula=Surv(T, d)~X, data=data)
fitIV <- ivcoxph(estmethod="ts", fitX=fitX, fitT=fitT, data=data, ctrl=TRUE)
summary(fitIV)

#G-estimation with non-parametric model for S(t|L,Z,X)
fitT <- survfit(Surv(T, d)~X+Z, data=data)
fitIV <- ivcoxph(estmethod="g", Z="Z", X="X", T="T", fitT=fitT, data=data, t=1)
summary(fitIV)

#G-estimation with Cox model for \lambda(t|L,Z,X)
fitT <- coxph(Surv(T, d)~X+X+X*Z, data=data)
fitIV <- ivcoxph(estmethod="g", Z="Z", X="X", T="T", fitT=fitT, data=data, t=1)
summary(fitIV)

}
