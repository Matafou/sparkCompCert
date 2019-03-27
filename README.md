# dependencies

- coq v8.x (9?)
- Compcert (32 bit)
    - menhir
  If from source "make depend backend/Cminor.vo cfrontend/Ctypes.vo" is sufficient.
- sparkformal
  If from source make eval.vo is sufficient.

# to compile
```
./configure.sh -spark <path to>/sparkformal/spark2014_semantics/src -compcert <path toW/CompCert 
```
use:
```
./configure.sh -reuseconf
```
if you want to reuse the previous options (stored in .config).
