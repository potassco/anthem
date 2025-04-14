# Installing From Crates.io
tbd

# Installing From Source
Linux users can build `anthem` directly from source, as follows.

```
    git clone https://github.com/potassco/anthem.git && cd anthem
    cargo build --release
    cp anthem/target/release/anthem ~/.local/bin
```

Note that you will also need a working installation of `vampire.`
Installation instructions can be found [here](https://vprover.github.io/).

# Installing with Docker
In our experience, building `vampire` on MacOS is tricky.
Mac users may prefer to install and run `anthem` with [Docker](https://www.docker.com/), as follows.

```
    git clone https://github.com/potassco/anthem.git && cd anthem
    docker build -t anthem 
    docker run -it --name anthem-container anthem /bin/bash
```
