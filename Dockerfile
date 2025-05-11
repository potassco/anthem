FROM ubuntu:22.04

RUN apt update
WORKDIR /root/

RUN apt install -y build-essential
RUN apt install -y curl
RUN apt install -y wget
RUN apt install -y git
RUN apt-get install -y vim

# Install Rust and Cargo
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y

# Install Vampire v4.9 (statically linked)
RUN wget https://github.com/vprover/vampire/releases/download/v4.9casc2024/vampire
RUN mv vampire /usr/bin/
RUN chmod +x /usr/bin/vampire

# Install Anthem
RUN git clone https://github.com/potassco/anthem.git
RUN cd anthem && git checkout zach/counting && . "$HOME/.cargo/env" && cargo build --release
RUN cp anthem/target/release/anthem /usr/bin/
