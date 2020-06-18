# Formalising Sigma Protocols and Commitment in EasyCrypt

## Prerequisites 
This work is known to work with EasyCrypt built from GIT hash: 132968e41afcc3a9834a9f12d19cbcbae0546535


The code can be found in the "code/" subfolder.

## SigmaProtocols.eca
Contains an abstract specification of Sigma Protocols and their security definitions. Also contains a proof Fiat-Shamir.

## Commitment.ec
Contains an abstract specification of Commitment Schemes and their security definitions.

## IdealCommitment.ec
Abstract specification of key-less commitment schemes

## PedersenCommit.ec
Formalisation of the Pedersen Commitment Scheme

## schnorr.rc
Formalisation of Schnorr's protocols.

## ANDProtocol.ec
Proof of the AND compound Sigma-protocol.

## ORProtocol.ec
Proof of the OR compound Sigma-protocol.

## Decompose.ec
Formalisation of arithmetic circuits and the (2,3)-Decomposition.

## ZKBoo.ec
Formalisation of the ZKBoo protocol. Depends on SigmaProtocols.eca, IdealCommitment.ec, and Decompose.ec
