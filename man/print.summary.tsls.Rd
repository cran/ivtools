\name{print.summary.tsls}

\alias{print.summary.tsls}

\title{
Prints summary of two-stage least squares estimation
}

\description{
This is a \code{print} method for class \code{"summary.tsls"}.
}

\usage{
\method{print}{summary.tsls}(x, digits=max(3L, getOption("digits")-3L), 
  signif.stars=getOption("show.signif.stars"), ...)
}

\arguments{
  \item{x}{
an object of class \code{"summary.tsls"}.
}
  \item{digits}{
the number of significant digits to use.
}
  \item{signif.stars}{
logical. If TRUE, "significance stars" are printed for each coefficient.
}
  \item{\dots}{
not used.
}
}

\author{
Arvid Sjolander
}

\seealso{
\code{\link{tsls}}
}

\examples{

##See documentation for tsls

}
