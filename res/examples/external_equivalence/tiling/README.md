# `tiling`


## Origin

Vladimir Lifschitz, student examples.

## Usage
```
anthem verify --equivalence external -m 4 tiling.{1.lp,2.lp,ug,U.po} -t 200
```
or, using the same proof outline divided into two files,
```
anthem verify --equivalence external -m 4 tiling.{1.lp,2.lp,ug,F.po} -t 100 --direction forward
anthem verify --equivalence external -m 4 tiling.{1.lp,2.lp,ug,B.po} -t 200 --direction backward
```
