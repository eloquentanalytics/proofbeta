# Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
# Build both engines from source, check them, and ship them in a minimal image.
#
#   docker build --build-arg REVISION="$(git rev-parse HEAD)" --build-arg REPO_URL="$(git remote get-url origin)" -t proofbeta .
#   docker run -i --rm proofbeta < corpus/sessions/work-rules.in.jsonl                              # the work engine
#   docker run -i --rm --entrypoint /stream-engine proofbeta < corpus/sessions/stream-rules.in.jsonl  # the core engine
#
# The build context has no .git, so the revision the engines report comes from the REVISION build argument (a full
# commit hash); without it they report "unknown". REPO_URL is recorded beside it ("unknown" without it).

FROM debian:bookworm-slim AS build
ARG TARGETARCH
# elan, pinned by version and checksum; it installs the Lean toolchain that lean-toolchain names.
ARG ELAN_VERSION=v4.2.4
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl && rm -rf /var/lib/apt/lists/*
RUN set -eu; \
    case "$TARGETARCH" in \
      amd64) arch=x86_64;  sum=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63 ;; \
      arm64) arch=aarch64; sum=05febd124d84ebf994b2e7479922a5650b1e950c17ae3bd1ddd776b65bb72bf9 ;; \
      *) echo "unsupported architecture: $TARGETARCH" >&2; exit 1 ;; \
    esac; \
    curl -sSfL -o /tmp/elan.tar.gz "https://github.com/leanprover/elan/releases/download/$ELAN_VERSION/elan-$arch-unknown-linux-gnu.tar.gz"; \
    echo "$sum  /tmp/elan.tar.gz" | sha256sum -c -; \
    tar -xzf /tmp/elan.tar.gz -C /tmp; \
    /tmp/elan-init -y --no-modify-path --default-toolchain none; \
    rm -f /tmp/elan.tar.gz /tmp/elan-init
ENV PATH=/root/.elan/bin:$PATH
WORKDIR /src
COPY lean-toolchain ./
RUN elan toolchain install "$(cat lean-toolchain)" && elan default "$(cat lean-toolchain)"
COPY . .
ARG REVISION=""
ARG REPO_URL=""
RUN PROOFBETA_REVISION="$REVISION" PROOFBETA_REPO_URL="$REPO_URL" scripts/stamp_revision
RUN lake build
# The checks that need nothing but the engines: the self-tests, then the corpus, byte for byte.
RUN .lake/build/bin/stream-engine --self-test \
 && .lake/build/bin/work-engine --self-test \
 && corpus/replay \
 && .lake/build/bin/work-engine --revision

FROM gcr.io/distroless/cc-debian12:nonroot
COPY --from=build /src/.lake/build/bin/work-engine /work-engine
COPY --from=build /src/.lake/build/bin/stream-engine /stream-engine
ENTRYPOINT ["/work-engine"]
