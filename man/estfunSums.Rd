\name{estfunSums}

\alias{estfunSums}

\title{
Evaluates the estimating function sum for \code{"ivglm"} and \code{"ivah"} 
objects, fitted with \code{method="g"}.
}

\description{
\code{estfunSums} evaluates the estimating function sum \eqn{\sum_{i=1}^n H_i(\psi)}
for a \code{"ivmod"} object, fitted with \code{method="g"}, 
at specified values of \eqn{\psi}.
}     

\usage{
estfunSums(object, psi)
}

\arguments{
\item{object}{
an object of class \code{"ivmod"}, fitted with \code{method="g"}.   
}
  \item{psi}{
either a vector or a matrix containing values of \eqn{\psi}. If \code{psi} is a 
matrix, then it is assumed that \eqn{\psi} is a vector and that each row of 
\code{psi} corresponds to one value of \eqn{\psi}. 
}

}

\details{ 
\code{estfunSums} may be useful for visual inspection of the estimating 
function, to make sure that a solution to the estimating equation 
\deqn{\sum_{i=1}^n H_i(\psi)=0}
was found, see `Examples'. 
 
}

\value{
\code{estfunSums} returns a vector (if \code{psi} is a vector), or a matrix 
(if \code{psi} is a matrix) containing the estimating function sum \eqn{\sum_{i=1}^n H_i(\psi)}  
evaluated at \code{psi}.  
}

\references{
Burgess S, Granell R, Palmer TM, Sterne JA, Didelez V. (2014). 
Lack of identification in semiparametric instrumental variable models with 
binary outcomes. \emph{American Journal of Epidemiology} \bold{180}(1), 111-119.
 
Vansteelandt S., Bowden J., Babanezhad M., Goetghebeur E. (2011). 
On instrumental variables estimation of causal odds ratios.
\emph{Statistical Science} \bold{26}(3), 403-422.

}


\author{
Arvid Sjolander. 
}

\examples{

require(survival)

set.seed(9)

##Note: the parameter values in the examples below are chosen to make 
##Y0 independent of Z, which is necessary for Z to be a valid instrument.

n <- 1000
psi0 <- 0.5

##---Example 1: logistic model--- 

Z <- rbinom(n, 1, 0.5)
X <- rbinom(n, 1, 0.7*Z+0.2*(1-Z)) 
m0 <- plogis(1+0.8*X-0.39*Z)
Y <- rbinom(n, 1, plogis(psi0*X+log(m0/(1-m0)))) 
data <- data.frame(Z, X, Y)

fitY <- glm(formula=Y~X+Z+X*Z, family="binomial", data=data)
fitIV <- ivglm(method="g", Z="Z", X="X", Y="Y", fitY=fitY, data=data, link="logit")
summary(fitIV)

psi <- seq(fitIV$est-1, fitIV$est+1, 0.1)
U <- estfunSums(object=fitIV, psi=psi)
plot(psi, U, type="l")
abline(h=0, lty="dashed")
abline(v=fitIV$est, lty="dashed")

##--Example2: Cox PH model

Z <- rbinom(n, 1, 0.5)
X <- rbinom(n, 1, 0.7*Z+0.2*(1-Z))
m0 <- plogis(1+0.8*X-0.34*Z) #Y0 independent of Z at t=1
T <- rexp(n, rate=exp(psi0*X+log(m0)))
d <- rbinom(n, 1, 0.2) #20% censoring
data <- data.frame(Z, X, T, d)

#G-estimation with non-parametric extimation of S(t|L,Z,X)
fitT <- survfit(Surv(T, d)~X+Z, data=data)
fitIV <- ivcoxph(method="g", Z="Z", X="X", T="T", fitT=fitT, data=data, t=1)
summary(fitIV)

psi <- seq(fitIV$est-1, fitIV$est+1, 0.1)
U <- estfunSums(object=fitIV, psi=psi)
plot(psi, U, type="l")
abline(h=0, lty="dashed")
abline(v=fitIV$est, lty="dashed")





}
