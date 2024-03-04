# Print available recipes
help:
    @just --list

# Format code
fmt:
    cargo +nightly fmt

# Lint code
lint:
    cargo clippy
    cargo +nightly fmt --check
    ./.local/cspell/bin/cspell --quiet --unique --gitignore --dot --cache '**'

# Install development tools
install:
    npm install --prefix=.local/cspell -g cspell
