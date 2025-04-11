# Command Line Tool

Anthem is primarily a translational tool -- it transforms ASP programs into theories written in the syntax of first-order logic.
Additional transformations within this syntax can sometimes produce theories whose classical models coincide with the stable models of the original program.
These transformations can be invoked via the command line using a variant of
```
    anthem translate --with <TRANSLATION>
```

Anthem can further exploit these translations from programs to equivalent (first-order) theories by invoking automated theorem provers to verify certain types of equivalence.
Variants of the
```
    anthem verify --equivalence <EQUIVALENCE>
```
command can produce problem files in the TPTP language accepted by many ATPs, or pass these problems directly to an ATP and report the results.

The automated verification of external equivalence is only applicable to certain mini-gringo programs.
The `analyze` command lets users check whether their program(s) meet these applicability requirements.
(Note that this is done automatically when the `verify` command is used).

For more details on these commands, and a list of available options, add the `--help` flag, e.g.
```
    anthem --help
    anthem translate --help
    anthem verify --help
    anthem analyze --help
    anthem simplify --help
```
