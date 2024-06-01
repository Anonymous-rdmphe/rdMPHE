# rdMPHE
This anonymous repository provides an implementation of the Reusable Dynamic Multi-Party Homomorphic Encryption (rdMPHE) scheme represented in a PoPETs submission. 
This library is built upon (https://github.com/SNUCP/snu-mghe, from https://github.com/SNUCP/MKHE-KKLSS) and Lattigo v2.3.0(https://github.com/tuneinsight/lattigo/tree/v2.3.0).

LICENSE
===============
Attribution-NonCommercial 2.0 Generic (CC BY-NC 2.0)

HOW TO INSTALL
==============
use "go mod vendor" 


HOW TO RUN UNITTEST
===================
1. go to target folder (e.g for rdMPHE/MKHE with CKKS [resp. BFV], "cd mkckks/" [resp. "cd mkbfv/"])
2. run go test command "go test -args -n=1"
