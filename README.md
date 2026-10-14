# anthem

`anthem` is a command-line application for assisting in the verification of answer set programs.
It operates by translating answer set programs written in the mini-gringo dialect of [clingo](https://potassco.org/clingo/) into many-sorted first-order theories.
Using automated theorem provers, `anthem` can then verify properties of the original programs, such as strong and external equivalence.

## Installation

`anthem` is available on [crates.io](https://crates.io/crates/anthem). Install it by running

``` sh
cargo install anthem
```

Alternatively, install it from source by cloning the repository and running

``` sh
cargo build --release
```

Note that `anthem` requires a working installation of [`vampire`](https://vprover.github.io/).
See the installation section of the [manual](https://docs.potassco.org/anthem/) for details and additional installation options.

To replicate the experimental setup from our publications, see the [Benchmark Setup](https://docs.potassco.org/anthem/benchmarks.html) section of the manual.

## Documentation

Check out the [Manual](https://docs.potassco.org/anthem/) to learn how to use `anthem`.

If you want to use `anthem` as a library to build your own application, you can do so.
Check out the [API documentation](https://docs.rs/anthem/) for the available functionalities.

## Examples

Example verification problems are grouped by equivalence (strong or external) within the [res/examples](res/examples) directory.
For example, visit the [cover](res/examples/external_equivalence/cover) directory for instructions on how to compare a program solving the Exact Cover problem [cover.1.lp](res/examples/external_equivalence/cover/cover.1.lp) against a first-order specification [cover.spec](res/examples/external_equivalence/cover/cover.spec).

## Where's anthem 1?

Until recently, you would have found Patrick Lühne's version 1 of `anthem` here, which was discontinued and therefore moved to [anthem-1](https://github.com/potassco/anthem-1).
You are currently looking at version 2, which is the latest version and the only one that is actively developed.
This version is a complete reimplementation of the original system with significantly extended capabilities.
It was started by Zach Hansen and Tobias Stolzmann, but is now being developed by a growing [group of people](CONTRIBUTORS.md).
We'd like to thank Patrick for the effort he put into his implementation and the kindness of resolving the naming conflict with us.

## License

`anthem` is distributed under the terms of the MIT license.
See [LICENSE](LICENSE) for details!

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in `anthem` by you shall be licensed as above, without any additional terms or conditions.
