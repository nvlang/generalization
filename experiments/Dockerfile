# Reproduction environment for the generalization linter's Mathlib sweep. See experiments/README.md.
#
#   docker build --build-arg GL_REVISION="$(git rev-parse HEAD)" -t gl-repro -f experiments/Dockerfile .
#   docker run --rm -v "$PWD/out:/out" gl-repro
# amd64 is explicit because the elan tarball below is x86_64: on an arm64 host this runs emulated.
FROM --platform=linux/amd64 ubuntu:24.04@sha256:4fbb8e6a8395de5a7550b33509421a2bafbc0aab6c06ba2cef9ebffbc7092d90

RUN apt-get update && apt-get install -y --no-install-recommends \
        curl git ca-certificates python3 libgmp-dev \
    && rm -rf /var/lib/apt/lists/*

# A pinned release tarball, not the master installer, so the image does not depend on its build date.
ENV ELAN_HOME=/opt/elan PATH=/opt/elan/bin:$PATH ELAN_VERSION=v4.2.3
RUN curl -sSfL "https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-x86_64-unknown-linux-gnu.tar.gz" \
      | tar -xz -C /tmp \
    && /tmp/elan-init -y --default-toolchain none \
    && rm /tmp/elan-init

WORKDIR /work
# Manifest first, so dependency resolution caches independently of linter edits. `cache get` fetches
# Mathlib's prebuilt oleans; without it the image would compile Mathlib from source.
COPY lean-toolchain lakefile.toml lake-manifest.json ./
RUN elan toolchain install "$(cat lean-toolchain)" && elan default "$(cat lean-toolchain)"
RUN lake exe cache get

# Both: the lean_lib declares no `roots`, so lake resolves the library name to ./GeneralizationLinter.lean.
COPY GeneralizationLinter.lean ./
COPY GeneralizationLinter/ ./GeneralizationLinter/
RUN lake build GeneralizationLinter

# After the expensive layers, so a changing revision does not invalidate `cache get`.
ARG GL_REVISION=unknown
ENV GL_REVISION=${GL_REVISION}
LABEL org.opencontainers.image.revision=${GL_REVISION}
LABEL org.opencontainers.image.description="Generalization linter Mathlib sweep, reproduction environment"

COPY experiments/run.py ./
# JOBS is deliberately unset: run.py sizes it to available memory, and over-subscribing loses data
# rather than time. Give the container memory instead.
ENV THREADS=2 OUT=/out
ENTRYPOINT ["python3", "/work/run.py"]
