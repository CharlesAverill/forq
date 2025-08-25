# Frocq

A formalization of Forth in Rocq for verification of critical embedded systems.

## Meta

- Author(s):
  - Charles Averill [<img src="https://zenodo.org/static/images/orcid.svg" height="14px" alt="ORCID logo" />](https://orcid.org/ORCID) (initial)
- License: [Not set](./)
- Compatible Coq versions: 8.19.1 or later
- Additional dependencies:
  - [Dune](https://dune.build) 2.5 or later
- Coq namespace: `Frocq`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of DNAml
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-Frocq
```

To instead build and install manually, do:

``` shell
git clone https://github.com/GH_UCharles Averill/Frocq.git
cd Frocq
dune build
dune install
```
