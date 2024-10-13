FROM coqorg/coq:8.16

SHELL ["/bin/bash", "-c"]

RUN sudo apt-get update && \
    sudo env DEBIAN_FRONTEND=noninteractive \
      apt-get install -y libffi-dev libncurses5 libncurses-dev libtinfo5 \
        zlib1g-dev libfuse-dev && \
    sudo rm -rf /var/lib/apt/lists/*

RUN curl -L https://downloads.haskell.org/~ghcup/x86_64-linux-ghcup -o ~/ghcup && \
    chmod +x ~/ghcup && \
    ~/ghcup install ghc 8.10.7 && \
    ~/ghcup install cabal 3.10.3.0 && \
    ~/ghcup set ghc 8.10.7 && \
    ~/ghcup set cabal 3.10.3.0 && \
    ~/ghcup gc --profiling-libs --share-dir --cache --tmpdirs && \
    rm -f ~/ghcup

ENV PATH="/home/coq/.cabal/bin:/home/coq/.ghcup/bin:$PATH"

RUN cabal update && \
    cabal install --lib rdtsc digest

RUN opam update -y -u && \
    opam install -y -v ocaml-lsp-server ocamlformat && \
    opam clean -a -c -s --logs

CMD ["/bin/bash"]
