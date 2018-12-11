\docType{data}

\name{VitD}

\alias{VitD}

\title{Data from a cohort study on Vitamin D and mortality.}

\format{The dataset contains the following variables:
\describe{
\item{age}{age at baseline.} 
\item{filaggrin}{binary indicator of whether the subject has mutations in the filaggrin gene.}
\item{vitd}{vitamin D level at baseline, measured as serum 25-OH-D (nmol/L).}
\item{time}{follow-up time.}
\item{death}{indicator of whether the subject died during follow-up.}
}
}

\usage{
data(VitD)
}
\description{
This dataset originates from a real cohort study on Viatmin D and mortailty,
described by Martinussen et al (2017). However, to allow public availability 
the data were slightly mutialted before inclusion in the 
\code{ivtools} package.    
}

\references{

Martinussen T., Sorensen D.D., Vansteelandt S. (2017). 
Instrumental variables estimation under a structural Cox model.
\emph{Biostatistics} <doi:10.1093/biostatistics/kxx057>.
}