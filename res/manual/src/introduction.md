# Introduction

Welcome to the latest system developed as part of the “ASP + Theorem Proving" (`anthem`) project!
This system consolidates the findings and functionalities of previous prototypes into a more stable tool for verifying ASP programs. 
The theory behind ANTHEM has been given a thorough treatment in the ASP literature -- if you are interested, the papers on [verifying strong equivalence](https://www.cs.utexas.edu/~ai-lab/pub-view.php?PubID=128026), [checking programs against specs](https://www.cs.utexas.edu/~ai-lab/pub-view.php?PubID=127836), and [program to program verification](https://www.cs.utexas.edu/~ai-lab/pub-view.php?PubID=127994) are good starting points.

As the name suggests, `anthem` is a tool for automated verification of ASP programs.
For a broad class of [clingo](https://potassco.org/clingo/) and ASP-Core-2 programs, `anthem` can translate a program into a set of formulas written in the syntax of first-order logic.
Given a specification (written in first-order logic or as another ASP program), `anthem` can automatically check certain types of equivalence hold between a program of interest and the specification by invoking the automated theorem prover `vampire`.

If you wish to experiment with `anthem` through a web interface, we provide one [here](https://anthem.unomaha.edu/).
