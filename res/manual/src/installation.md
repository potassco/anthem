# Installing From Crates.io
The `anthem` crate and installation instructions can be found [here](https://crates.io/crates/anthem).

# Installing From Source
Linux users can build `anthem` directly from source, as follows.

```
    git clone https://github.com/potassco/anthem.git && cd anthem
    cargo build --release
    cp target/release/anthem ~/.local/bin
```

Note that you will also need a working installation of `vampire.`
Installation instructions can be found [here](https://vprover.github.io/).

# Installing with Docker
In our experience, building `vampire` on MacOS is tricky.
Non-Linux users may prefer to install and run `anthem` with [Docker](https://www.docker.com/).
Make sure Docker is running then run the following commands.

```
    git clone https://github.com/potassco/anthem.git && cd anthem
    docker build -t anthem .
    docker run -it --name anthem-container anthem /bin/bash
```
Now you can run your `anthem` commands in the interactive Docker terminal.
Try ``anthem --help`` to get started or ``ls anthem/res/examples`` to see available examples.
