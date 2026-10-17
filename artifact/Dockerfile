# Artifact image for the TRIEL 2.5 core.
#
# Build from the repository root:
#   docker build -f artifact/Dockerfile -t triel-artifact .
# Run everything that CI checks:
#   docker run --rm triel-artifact
#
# Both base images are pinned by digest.

# GHC 9.6.7, the version of .github/workflows/evaluator.yml. Only the
# installed GHC under /opt/ghc/9.6.7 is taken from this image.
FROM haskell:9.6.7-slim@sha256:3abe1175a5466fe760ed90937b32b42be340281b6707dace6d5addea2148d05e AS ghc

# Isabelle2025-2 on Ubuntu 24.04, with the HOL heap already built.
FROM makarius/isabelle:Isabelle2025-2@sha256:9bd33b183c399327c5d554fc8cde27c29b5d2b20cdc6fe7a604caa3f951018fc

USER root

# A C toolchain and the libraries GHC links against; Python 3.12 is the
# python3 of Ubuntu 24.04.
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      binutils gcc libc6-dev libffi-dev libgmp-dev libnuma-dev make \
      python3 python3-venv \
 && rm -rf /var/lib/apt/lists/*

# Documentation and profiling libraries are not needed to build the evaluator.
COPY --from=ghc /opt/ghc/9.6.7 /opt/ghc/9.6.7
RUN rm -rf /opt/ghc/9.6.7/share/doc \
 && find /opt/ghc/9.6.7 \( -name '*.p_hi' -o -name '*_p.a' -o -name '*.p_o' \) -delete

COPY artifact/requirements.txt /tmp/requirements.txt
RUN python3 -m venv /opt/venv \
 && /opt/venv/bin/pip install --no-cache-dir --require-hashes -r /tmp/requirements.txt \
 && rm /tmp/requirements.txt

ENV PATH=/opt/venv/bin:/opt/ghc/9.6.7/bin:/home/isabelle/Isabelle/bin:$PATH

COPY --chown=isabelle:isabelle . /home/isabelle/triel

USER isabelle
WORKDIR /home/isabelle/triel

# Print the tool versions at build time, so that the build log records them.
RUN isabelle version && ghc --numeric-version && python3 --version \
 && python3 -c 'import importlib.metadata as m; print("lark", m.version("lark"), "pytest", m.version("pytest"))'

ENTRYPOINT ["/home/isabelle/triel/artifact/run.sh"]
