# anthem

`anthem` is a command line application for translating answer set programs in the mini-gringo dialect of [clingo](https://potassco.org/clingo/) to first-order theories.
Using an automated theorem prover, these theories can then be used to verify properties of the original programs, such as strong and external equivalence.

Check out the [Manual](https://potassco.org/anthem/) to learn how to install and use `anthem`.

If you want to use `anthem` as a library to build your own application, you can do so.
Check out the [API documentation](https://docs.rs/anthem/) for the available functionalities.

## Where's anthem 1?

You're currently looking at version 2 of `anthem`, which is the latest version and the only one that is actively developed.
This is a complete reimplementation of the original system with significantly extended capabilities: we would like to thank everyone in the list of `contributors` for making it possible.

Until recently, you would have found Patrick Lühne's version 1 here, which was discontinued and therefore moved to [anthem-1](https://github.com/potassco/anthem-1).
We'd like to thank Patrick for the effort he put into his implementation and the kindness of resolving the naming conflict with us.

## License

`anthem` is distributed under the terms of the MIT license.
See [LICENSE](LICENSE) for details!

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in `anthem` by you shall be licensed as above, without any additional terms or conditions.
