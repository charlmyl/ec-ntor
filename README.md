# EasyCrypt Formalization of the NTOR Protocol

## Project Structure

The `ntor` folder contains the various EasyCrypt files that make-up the proof and definitions.
Below we outline what each contains:
- `Games.ec`: the implementation of all intermediate games.
- `ModelRelations.ec`: the proofs for the equivalence between the unrestricted and restricted name-based model and reduction from restricted name-based to restricted public-key-only security in the setting of NTOR. 
- `NTOR_name.ec`: the definition of the simplified NTOR protocol.
- `NTOR_pkonly.ec`: the definition of the modified NTOR protocol using only public keys instead of names as server identifiers.
- `Security.ec`: the proofs for all game hops and the statement for restricted public-key-only security of the modified NTOR protocol including reductions and supporting lemmas. 
- `UAKE_name.eca`: the implementation of the restricted and unrestricted name-based models.
- `UAKE_pkonly.eca`: the implementation of the restricted public-key-only model.

## Key Theorems and Security Statement

Section 2
- Theorem 1, From restricted to unrestricted security applied to the simplified NTOR protocol: `ntor/ModelRelations.ec` line ?
- Theorem 2, From unrestricted to restricted security applied to the simplified NTOR protocol: `ntor/ModelRelations.ec` line ?
- Theorem 3, From restricted name-based security of the simplified NTOR protocol to restricted public-key-only security of the modified NTOR protocol: `ntor/ModelRelations.ec` line ?

Section 4
- Theorem 5, Restricted public-key-only security of the modified NTOR protocol: `ntor/Security.ec` line 19000

## Compiling the Project

This project has been verified with EasyCrypt (r2026.02) along with the following provers:
- Alt-Ergo 2.6.3
- CVC5 1.0.9
- CVC4 1.8
- Z3 4.12.6

To compile, first install the above provers and EasyCrypt. Then simply run `make check`.

### Docker

For ease, one can also make use of the EasyCrypt docker image.
In the project directory, run

```
docker run -v .:/home/charlie/ntor -it ghcr.io/easycrypt/ec-test-box:r2026.02
```

to enter the test box. Then to compile

```
cd ntor && opam exec -- make check
```
