\name{tsls}

\alias{tsls}

\title{
Two-stage least squares estimation of the causal exposure effect in 
instrumental variables scenarios 
}

\description{
\code{tsls} computes the two-stage least squares (aka Wald) estimate 
of the causal exposure effect in instrumental variables scenarios. Let \eqn{Y}, \eqn{X}, 
and \eqn{Z} be the outcome, exposure, instrument, respectively. Let \eqn{L} be a vector 
of covariates that we wish to control for in the analysis. The user
supplies a fitted generalized linear model (GLM) for \eqn{E(X|Z,L)} and 
a fitted GLM for \eqn{E(Y|X,L)}. \code{tsls} uses 
the GLM for \eqn{E(X|Z,L)} to construct predictions
\eqn{\hat{X}}. These predictions are subsequently used to re-fit the GLM for 
\eqn{E(Y|X,L)}, with \eqn{X} replaced with \eqn{\hat{X}}. The obtained coefficient(s)
for \eqn{X} is the estimated causal effect. 
}     

\usage{
tsls(fitX, fitY, control=FALSE, data, clusterid)
}

\arguments{
  \item{fitX}{
an object of class \code{"glm"}, as returned by the \code{glm} function 
  in the \code{stats} package. This is the fitted GLM for \eqn{E(X|Z,L)}.
}
\item{fitY}{
an object of class \code{"glm"}, as returned by the \code{glm} function 
  in the \code{stats} package. This is the fitted GLM for \eqn{E(Y|X,L)}. 
The model is assumed to have a specific form, see details below.  
}
  \item{control}{
should the control function \eqn{R=X-\hat{X}} be used when re-fitting 
the GLM for \eqn{E(Y|X,L)}? 
}
  \item{data}{
a data frame containing the variables in the model. The outcome, exposure,
instrument and covariates can have arbitrary names, e.g. they don't need to 
be called \code{Y}, \code{X}, \code{Z} and \code{L}.
}
  \item{clusterid}{
an optional string containing the name of a cluster identification variable when 
data are clustered. 
}

}

\details{ 
Let \eqn{\eta} be the link function in the GLM for \eqn{E(Y|X,L)}. The model should be on 
the form 
\deqn{\eta\{E(Y|X,L)\}=m(L;\psi)X+g(L;\beta),} 
e.g. \eqn{E(Y|X,L)=\psi X+\beta_0+\beta_1 L} or 
\eqn{E(Y|X,L)=\psi_0 X+\psi_1 XL+\beta_0+\beta_1 L}. Let \eqn{\hat{\psi}_{tsls}} be the 
two-stage least squares estimator of \eqn{\psi}, i.e. the MLE of \eqn{\psi} 
when \eqn{X} is replaced by \eqn{\hat{X}} in the model. Let \eqn{Y_x} be the 
potential outcome for a given subject, under exposure level \eqn{X=x}.
\eqn{\hat{\psi}_{tsls}} can be interpreted in at least two different ways.   
If \eqn{\eta} is the identity link, \eqn{Z} is a valid instrument,
and the causal (structural nested) model 
\deqn{A: \eta\{E(Y|X,Z,L)\}-\eta\{E(Y_0|X,Z,L)\}=m(L;\psi^*)X} 
holds, then \eqn{\hat{\psi}_{tsls}} is consistent for \eqn{\psi^*} in this model.
Further, let \eqn{U} be the set of all confounders for the exposure-outcome association.
If \eqn{\eta} is the identity link, \eqn{Z} is a valid instrument, and
the causal model 
\deqn{B: \eta\{E(Y_x|L,U)\}-\eta\{E(Y_0|L,U)\}=m(L;\psi^{**})X} 
holds, then \eqn{\hat{\psi}_{tsls}} is consistent for \eqn{\psi^{**}} in this model. 
When \eqn{\eta} is the identity link, model B implies model A, but not the other way around.  
When \eqn{\eta} is not the identity link,
\eqn{\hat{\psi}_{tsls}} is generally inconsistent for both \eqn{\psi^*} and \eqn{\psi^{**}},
even if \eqn{Z} is a valid instrument and models A and B hold. 
The bias is often reduced by using the control function \eqn{R=X-\hat{X}} as an 
additional regressor when refitting the GLM for \eqn{E(Y|X,L)}. We refer to 
Vansteelandt et al (2011) for a thorough review of the underlying assumptions,
the interpretation, and the asymptotic properties of \eqn{\hat{\psi}_{tsls}}.  
}

\value{
An object of class \code{"tsls"} is a list containing 
\item{est}{
  a vector containing the two-stage least squares estimate \eqn{\hat{\psi}_{tsls}}. 
  }
\item{vcov}{
  the variance-covariance matric for the two-stage least squares estimate \eqn{\hat{\psi}_{tsls}}, 
obtained with the sandwich formula. 
  }
}

\note{
  \code{tsls} does not currently handle missing data.
}

\references{
Vansteelandt S., Bowden J., Babanezhad M., Goetghebeur E. (2011). 
\emph{On instrumental variables estimation of causal odds ratios} \bold{26}(3), 403-422.
}

\author{
Arvid Sjolander. 
}

\examples{

##Example 1: identity link and no interaction
n <- 1000
psi <- 0.5
U <- rnorm(n) #confounder for X and Y
L <- rnorm(n) #confounder for Z and Y
Z <- rnorm(n) #instrument
X <- rnorm(n, mean=Z+L+U) #exposure 
Y <- rnorm(n, mean=psi*X+L+U) #outcome
data <- data.frame(L, Z, X, Y)
fitX <- glm(X~Z+L, data=data)
fitY <- glm(Y~X+L, data=data)
fitIV <- tsls(fitX=fitX, fitY=fitY, data=data)
summary(fitIV)

##Example 2: logistic link and interaction between X and L
n <- 1000
psi0 <- 1
psi1 <- 0.5
U <- rnorm(n) #confounder for X and Y
L <- rnorm(n) #confounder for Z and Y
Z <- rnorm(n) #instrument
X <- rnorm(n, mean=Z+L+U) #exposure
Y <- rbinom(n, 1, plogis(psi0*X+psi1*X*L+L+U)) #outcome
data <- data.frame(L, Z, X, Y)
fitX <- glm(X~Z+L, data=data)
fitY <- glm(Y~X+L+X*L, data=data, family="binomial")
fitIV <- tsls(fitX=fitX, fitY=fitY, data=data, control=TRUE)
summary(fitIV)


}
