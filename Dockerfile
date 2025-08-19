FROM ubuntu:22.04

WORKDIR /natt

RUN apt update && apt install -y default-jre z3 opam

RUN opam init -y --disable-sandboxing &&\
	opam install -y ocamlfind ocamlgraph re &&\
	opam install -y xml-light

COPY . .

RUN eval $(opam env); make

ENV PATH $PATH:/natt/bin

RUN echo $PWD; echo $PATH