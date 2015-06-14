# Building and running the benchmark

Before building the benchmark, please make sure that you compiled the mapping database 
code to generate the extracted ocaml code (see parent directory).

To build the benchmark, use the following command:

```
$ ocamlbuild bench_random.native -I extract 
```

And then to run them:

```
$ ./bench_random.native
```

The output consists of 4 columns separated by ':':

```
<r>:<name>:<iterations>:<time>
```

`name` is the name of the implementation (avl for the avl trees, assoc for the associative 
lists). `r` is just the result of a lookup, to make sure that the ocaml optimizer 
doesn't optimize the benchmark loop away. `iterations` and `time` are the number of 
iterations and the total time needed for this number of iterations.
