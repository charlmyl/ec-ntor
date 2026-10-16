# EasyCrypt Formalization of the NTOR Protocol

## Project Structure

The `ntor` folder contains the various EasyCrypt files that make-up the proof and definitions.
Below we outline what each contains:
- `Games.ec`: the implementation of all intermediate games.
- `ModelRelations.ec`: the proofs for the equivalence between the name-based model with and without dishonest servers and reduction from name-based to public-key-only security with only honest servers in the setting of NTOR. 
- `NTOR_name.ec`: the definition of the simplified NTOR protocol.
- `NTOR_pkonly.ec`: the definition of the modified NTOR protocol using only public keys instead of names as server identifiers.
- `Security.ec`: the proofs for all game hops and the statement for public-key-only security with only honest servers of the modified NTOR protocol including reductions and supporting lemmas. 
- `UAKE_name.eca`: the implementation of the name-based models with and without dishonest servers.
- `UAKE_pkonly.eca`: the implementation of the public-key-only model with only honest servers.

## Key Theorems and Security Statement

Section 2
- Theorem 1, From name-based security with only honest servers to name-based security with dishonest servers applied to the simplified NTOR protocol: `ntor/ModelRelations.ec` line 936
- Theorem 2, From name-based security with dishonest servers to name-based security with only honest servers applied to the simplified NTOR protocol: `ntor/ModelRelations.ec` line 1833
- Theorem 3, From name-based security with only honest servers of the simplified NTOR protocol to public-key-only security with only honest servers of the modified NTOR protocol: `ntor/ModelRelations.ec` line 3339

Section 4
- Theorem 5, Public-key-only security with only honest servers of the modified NTOR protocol: `ntor/Security.ec` line 19103

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
