## InnoChain smart contract
InnoChain smart contract is a HOL4 model which is translated into AST of CakeML.

## Build instructions

Obtaining CakeML infrastructure without Docker:

<b>Built with</b>
- [CakeML](https://github.com/CakeML/cakeml/commit/311f6e9de8151110c5a522b552a599b25d61ddeb)
- [HOL4](https://github.com/HOL-Theorem-Prover/HOL/commit/0aae6443b97e2d1bd0ea728d27ca72d0913aa763)

All succesfull tests are availible in https://cakeml.org/regression.cgi/queue/finished

Steps:
1.  apt-get update && \
    apt-get install -y bash gcc g++ git make && \
    apt-get clean
2. git clone https://github.com/polyml/polyml && \
    cd polyml && \
    git checkout v5.8.1 && \
    ./configure --prefix=/usr && \
    make && \
    make install
3. git clone https://github.com/HOL-Theorem-Prover/HOL && \
    cd HOL && \
    git checkout 0aae6443b97e2d1bd0ea728d27ca72d0913aa763 && \
    poly < tools/smart-configure.sml && \
    ./bin/build
4. git clone https://github.com/CakeML/cakeml && \
    cd cakeml && \
    git checkout 311f6e9de8151110c5a522b552a599b25d61ddeb && \
    ~/HOL/bin/Holmake

But since rebuilding HOL4-CakeML project requires quite a lot of memory (more than 15 GB of RAM),
so it is better to use ~/HOL/bin/Holmake in ~/cakeml/tutorial/solutions directory.

5. cd cakeml && \
    mkdir -p bin && \
    cp cake-x64-64.tar.gz bin/ && \
    cd bin && \
    tar xzf cake-x64-64.tar.gz && \
    rm -rf cake-x64-64.tar.gz
   If you didn't use ~/HOL/bin/Holmake to build all HOL4-CakeML project, then you should just download
   CakeML compiler -- https://cakeml.org/download.html

6. cd cakeml/examples && \
    ~/HOL/bin/Holmake

Optional step.

Obtaining CakeML infrastructure with Docker:
1. docker pull nvasiliev0/alexverification
2. docker run -it nvasiliev0/alexverification opam exec -- bash

Creating smart contract project:
1. Create a folder in the directory ~/cakeml/ and copy files baseScript.sml, baseProgScript.sml.
2. Copy Holmake file from ~/cakeml/tutorial/ into that folder.
3. Run ~/HOL/bin/Holmake in that folder.

After few minutes, you will get baseProgTheory.{dat|sig|sml|ui|uo} files, which are necessary to experiment with file baseProgScript.sml (translation to s-expression file) in Emacs, Vim or even jEdit
(more information about user-interface in https://hol-theorem-prover.org/hol-mode.html).

## Code Example

All functions of smart contracts are defined in standard HOL4 definitions:

> Definition name\_def:
>     name arguments = SML function
> End

It is simularly to datatypes:
> Datatype:
>     SML datatypes
> End

Example of translation to .S file from HOL4:

> val res = translate execute\_def;

> val state = get\_ml\_prog\_state();

get\_ml\_prog\_state(); returns the AST

> val prog\_tm = get\_prog (remove\_snocs(clean\_state(state)));

> val prog\_def = Define \` out\_prog = ^prog\_tm \`;

> val base\_compiled = save\_thm("out\_compiled", compile\_x64 "out" prog\_def);

That's it, conceptually there is nothing else here.

