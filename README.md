# Contents 

This repository contains soundness proofs for CSL (Concurrent Separation Logic) and RGSep, 
two program logics for reasoning about the correctness of concurrent programs.
The soundness proofs are carried out using the [Coq proof assistant](https://coq.inria.fr) version 8.6.

* HahnBase.v : Basic tactics (copied from the [Hahn](https://github.com/vafeiadis/hahn) library)
* Basic.v : Definition of heaps and basic lemmas about lists
* Lang.v : Definition of a simple programming language
* CSLsound.v : Soundness proof of CSL
* RGSepsound.v : Soundness proof of RGSep

For more details about the structure of the proof, please look at the following paper

* [Concurrent separation logic and operational semantics.](https://doi.org/10.1016/j.entcs.2011.09.029)
  Viktor Vafeiadis.
  In MFPS 2011. ENTCS 276, pp. 335-351. Elsevier (September 2011)

and at the paper's [webpage](https://people.mpi-sws.org/~viktor/cslsound/).

# Contact

* [Viktor Vafeiadis](https://people.mpi-sws.org/~viktor/), MPI-SWS, Germany

