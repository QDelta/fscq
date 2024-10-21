FROM debian:12-slim

SHELL ["/bin/bash", "-c"]

RUN apt-get update -y -q && \
    DEBIAN_FRONTEND=noninteractive apt-get install -y -q \
      autoconf automake bubblewrap build-essential ca-certificates \
      curl git less libgmp-dev m4 pkg-config \
      rlwrap rsync sudo time unzip \
      libffi-dev libncurses5 libncurses-dev libtinfo5 \
      zlib1g-dev libfuse-dev && \
    rm -rf /var/lib/apt/lists/*

RUN curl -fSL -o /usr/local/bin/opam "https://github.com/ocaml/opam/releases/download/2.2.1/opam-2.2.1-x86_64-linux" && \
    chmod a+x /usr/local/bin/opam

ARG UID=1000
ARG GID=1000

RUN (groupadd -g ${GID} coq || true) && \
    useradd --no-log-init -m -s /bin/bash -g ${GID} -G sudo -p '' -u ${UID} coq && \
    mkdir -m 775 -p -v /home/coq/.local/bin && \
    chown -R coq:${GID} /home/coq/.local

WORKDIR /home/coq
USER coq

RUN opam init --auto-setup --yes --bare --disable-sandboxing && \
    opam switch create default --package=ocaml-option-flambda,ocaml-variants.4.14.2+options && \
    eval $(opam env) && \
    opam repository add --all-switches --set-default coq-released https://coq.inria.fr/opam/released && \
    opam update -y && \
    opam install -y opam-depext && \
    opam pin add -n -k git coq.8.16.1 https://github.com/ejgallego/coq.git#v8.16+lsp && \
    opam install -y -v coq coq-bignums coq-serapi coq-lsp ocaml-lsp-server ocamlformat && \
    opam clean -a -c -s --logs && \
    chmod -R g=u /home/coq/.opam && \
    opam config list && opam list

ENTRYPOINT ["opam", "exec", "--"]

CMD ["/bin/bash"]