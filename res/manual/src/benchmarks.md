# Anthem 2.0 Experimental Setup
To replicate the `anthem` setup used in the ICLP'25 paper use the vampire version `v4.9casc2024` with `z3` linked.
Clone this version of vampire using

```
    git clone --recursive --branch v4.9casc2024 --depth=1 https://github.com/vprover/vampire.git
```

Then follow the [source build instructions](https://github.com/vprover/vampire/tree/v4.9casc2024#source-build).
Make sure to build `z3` first, as described [here](https://github.com/vprover/vampire/tree/v4.9casc2024#adding-z3).

`anthem` calls `vampire` from your `PATH`, so copy or symlink the built binary (`vampire_z3*`) to a directory on your `PATH` under the name `vampire`.
For example, from the `vampire` build directory run
```
    cp bin/vampire_z3* ~/.local/bin/vampire
```
