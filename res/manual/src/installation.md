# Installing From Crates.io
The `anthem` crate can be found [here](https://crates.io/crates/anthem).
Install it by running
```
    cargo install anthem
```

# Installing From Source
Alternatively, you can build `anthem` directly from source, as follows.

```
    git clone https://github.com/potassco/anthem.git && cd anthem
    cargo build --release
    cp target/release/anthem ~/.local/bin
```

# Installing Vampire
Note that you will also need a working installation of [`vampire`](https://vprover.github.io/).
Either use one of the pre-built binaries available [here](https://github.com/vprover/vampire/releases)
or install vampire from source using the instructions provided [here](https://github.com/vprover/vampire/wiki/Source-Build-for-Users).
We recommend building `vampire` with `z3` linked for better performance.

# Installing with Docker
If you experience issues building `vampire`, you may prefer to install and run `anthem` with [Docker](https://www.docker.com/).
Make sure Docker is running then run the following commands.

```
    git clone https://github.com/potassco/anthem.git && cd anthem
    docker build -t anthem .
    docker run -it --name anthem-container anthem /bin/bash
```
Now you can run your `anthem` commands in the interactive Docker terminal.
Try ``anthem --help`` to get started or ``ls anthem/res/examples`` to see available examples.
