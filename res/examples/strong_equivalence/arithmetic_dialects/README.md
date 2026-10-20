# `arithmetic_dialects`

| | clingo 5 | clingo 6 |
|---|---|---|
| `/` | rounds toward zero | rounds down |
| `\` | the remainder has the sign of the dividend | the remainder has the sign of the divisor |

`gringo_five.lp` and `gringo_six.lp` list the facts that clingo 5 and clingo 6 derive:

| | clingo 5 | clingo 6 |
|---|---|---|
| `7 / 2` | 3 | 3 |
| `7 / -2` | -3 | -4 |
| `-7 / 2` | -3 | -4 |
| `-7 / -2` | 3 | 3 |
| `7 \ 2` | 1 | 1 |
| `7 \ -2` | 1 | -1 |
| `-7 \ 2` | -1 | 1 |
| `-7 \ -2` | -1 | -1 |
