Implementation of Ranjit's algorithm from [this paper](https://dl.acm.org/doi/pdf/10.1145/1190215.1190260)

Used in combination with [expresso](https://arxiv.org/pdf/1804.02503.pdf)
to provide a benchmark for fine-grained locking on implicit monitors

Based on [SOOT](https://en.wikipedia.org/wiki/Soot_(software))

* `edu.<...>.utopia.lockPlacementBenchmarks` has the driver which reads in arguments from
  the command line, does analysis, and applies transformations
* `<...>.lockPlacementBenchmarks.zeroOneILPPlacement` is the beginning of Ranjit's algorithm
    - `<...>.expressoPP` Preprocessing from expresso: create condition variables
      associated to predicates and signal in the appropriate places.
      Do not initialize them/associate them to locks yet
    - `<...>.analysis` Analyze the preprocessed jimple file
    - `<...>.instrumentation` Associate conditions to locks and insert locks
