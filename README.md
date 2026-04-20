# anthem

`anthem` is a command-line application for assisting in the verification of answer set programs.
It operates by translating answer set programs written in the mini-gringo dialect of [clingo](https://potassco.org/clingo/) into many-sorted first-order theories.
Using automated theorem provers, `anthem` can then verify properties of the original programs, such as strong and external equivalence.

Check out the [Manual](https://potassco.org/anthem/) to learn how to install and use `anthem`.

If you want to use `anthem` as a library to build your own application, you can do so.
Check out the [API documentation](https://docs.rs/anthem/) for the available functionalities.

## Where's anthem 1?

Until recently, you would have found Patrick Lühne's version 1 of `anthem` here, which was discontinued and therefore moved to [anthem-1](https://github.com/potassco/anthem-1).
You are currently looking at version 2, which is the latest version and the only one that is actively developed.
This version is a complete reimplementation of the original system with significantly extended capabilities.
It was started by Zach Hansen and Tobias Stolzmann, but is now being developed by a growing [group of people](CONTRIBUTORS.md).
We'd like to thank Patrick for the effort he put into his implementation and the kindness of resolving the naming conflict with us.

## Examples
Examples of verification problems are grouped by equivalence (strong or external) within the [res/examples](res/examples) directory.
For example, visit the [cover](res/examples/external_equivalence/cover) directory for instructions on how to compare a program solving the Exact Cover problem [cover.1.lp](res/examples/external_equivalence/cover/cover.1.lp) against a first-order specification [cover.spec](res/examples/external_equivalence/cover/cover.spec).

## Replicating the Anthem 2.0 Experimental Setup

Clone the appropriate version of `vampire`:
```sh
$ git clone --recursive --branch v4.9casc2024 --depth=1 https://github.com/vprover/vampire.git
```

Build `z3`:
```sh
$ cd vampire/z3
$ mkdir build && cd build
$ cmake .. -DZ3_SINGLE_THREADED=1 -DCMAKE_BUILD_TYPE=Release
$ make
```

Now `cd` back to the `vampire` source directory and build `vampire`:
```sh
$ mkdir build && cd build
```

Change the installation directory (for example, `/usr/bin`) as needed when running cmake, e.g.
```sh
$ cmake .. -DCMAKE_INSTALL_PREFIX=/usr/bin
$ make
```

Copy the executable to your installation directory:
```sh
$ sudo cp bin/vampire_z3* <Your Installation Directory>/vampire
```

## License

`anthem` is distributed under the terms of the MIT license.
See [LICENSE](LICENSE) for details!

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in `anthem` by you shall be licensed as above, without any additional terms or conditions.
