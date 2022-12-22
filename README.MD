# Refinery

## About

Refinery is a hobby language based on the idea of refinement types. Refinement types are data types that have some added state information that is carried with them during type checking. The state information can be used to verify that the correct values are inputed in functions rather than relying on checking at runtime. A language that implements this is [Liquid Haskell](https://ucsd-progsys.github.io/liquidhaskell/). The hope is that Refinery can bring the ideas of refinement types to an imperitive language.

## Project Set Up (for cloning/modification)

1) if coq was installed using opam make sure to 
    ``` eval $(opam env) ```

2) in the project directory run:
    ```coq_makefile -f _CoqProject -o Makefile```

3) in the project directory create object files by running
    ```make all```
