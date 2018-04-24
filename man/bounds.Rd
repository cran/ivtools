\name{bounds}

\alias{bounds}

\title{
Bounds for the marginal causal risk difference in instrumental variables scenarios 
}

\description{
\code{bounds} computes non-parametric bounds for the marginal causal risk difference
in instrumental variables scenarios with binary variables. Let \eqn{Y}, \eqn{X}, and \eqn{Z} 
be the binary outcome, exposure, and instrument, respectively. Let \eqn{p(Y_x=1)} be the 
counterfactual probability of the outcome, had all subjects been exposed to level \eqn{x}.
\code{bounds} computes bounds for the marginal causal risk difference \eqn{p(Y_1=1)-p(Y_0=1)},
as well as bounds for the counterfactuals probabilities \eqn{p(Y_1=1)} and \eqn{p(Y_0=1)}
separately. 
}  

\usage{
bounds(data, Z, X, Y)
}

\arguments{
  \item{data}{
either a data frame containing the variables in the model, or a named vector  
\code{(p00.0,...,p11.1)} containing the eight probabilities 
\eqn{(p(Y=0,X=0|Z=0),...,p(Y=1,X=1|Z=1))}.
}
  \item{Z}{
a string containing the name of the instrument \eqn{Z} in \code{data}. Not specified if 
\code{data} is a vector of probabilities.
}
  \item{X}{
a string containing the name of the exposure \eqn{X} in \code{data}. Not specified if 
\code{data} is a vector of probabilities.
}
  \item{Y}{
a string containing the name of the outcome \eqn{Y} in \code{data}. Not specified if 
\code{data} is a vector of probabilities.
}

}

\details{
\code{bounds} uses linear programming techniques to bound the marginal causal risk difference. For details,
see Balke and Pearl (2009).  
}

\value{
An object of class \code{"bounds"} is a list containing 
\item{p0}{
  a vector containing the lower and upper bounds for \eqn{p(Y_0=1)}. 
  }
\item{p1}{
  a vector containing the lower and upper bounds for \eqn{p(Y_1=1)}. 
  }
\item{RD}{
  a vector containing the lower and upper bounds for \eqn{p(Y_1=1)-p(Y_0=1)}.
  }
}

\note{
  \code{bounds} does not currently handle missing data.
}

\references{
Balke, A. and Pearl, J. (1997). \emph{Bounds on treatment effects from studies with imperfect compliance}.
\emph{Journal of the American Statistical Association} \bold{92}(439), 1171-1176. 
}

\author{
Arvid Sjolander. 
}

\examples{

##Vitamin A example from Balke and Pearl (1997).
n0 <- 74+11514
n1 <- 34+12+2385+9663
p <- c(74/n0, 34/n1, 0, 12/n1, 11514/n0, 2385/n1, 0, 9663/n1)
names(p) <- c("p00.0", "p00.1", "p01.0", "p01.1", 
  "p10.0", "p10.1", "p11.0", "p11.1") 
bounds(data=p)

}
