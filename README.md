# dependencies

- coq v8.x (9?)
- Compcert (32 bit)
    - menhir
- sparkformal

# to compile
```
./configure.sh -spark <path to>/sparkformal/spark2014_semantics/src -compcert <path toW/CompCert 
```
use:
```
./configure.sh -reuseconf
```
if you want to reuse the previous options (stored in .config).
