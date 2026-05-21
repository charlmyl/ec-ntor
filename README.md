# EasyCrypt Formalisation of the NTOR Protocol

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
