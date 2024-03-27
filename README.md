# Reckle Trees

Reckle trees is a new vector commitment based on succinct RECursive arguments and MerKLE trees. Reckle
trees' distinguishing feature is their support for succinct batch proofs that are _updatable_.

This repository contains the circuits from the paper:

["_Reckle Trees: Updatable Merkle Batch Proofs with Applications_,"](http://lagrange.dev/reckle-trees)
[Charalampos Papamanthou](https://twitter.com/chbpap),
[Shravan Srinivasan](https://github.com/sshravan),
[Nicolas Gailly](https://github.com/nikkolasg),
[Ismael Hishon-Rezaizadeh](https://twitter.com/Ismael_H_R),
[Andrus Salumets](https://github.com/andrussal), and
[Stjepan Golemac](https://github.com/stjepangolemac).


### Instructions
``` bash
git clone git@github.com:Lagrange-Labs/reckle-trees.git
cd reckle-trees
rustup override set nightly-2024-01-21

cargo test rec_benches --release -- --nocapture # Optimized Reckle trees (Figure 4)
cargo test bucket_benches --release -- --nocapture # Optimized Reckle trees + bucketing (Section 3.7)
cargo test dt_benches --release -- --nocapture # Digest translation (Figure 7)
cargo test bls_benches --release -- --nocapture # BLS pk aggregation (Figure 8)

# Baseline: Monolithic circuits (Section 5.3)
cargo test dt_mono_benches --release -- --nocapture
cargo test bls_mono_benches --release -- --nocapture
```

Note:
- Modify `log_tree_sizes` and `log_subset_sizes` to set the tree sizes and the subset sizes, respectively
- Increase the sample size of the benchmarks to collect reliable measurements

### License
Please see the license [here](https://github.com/Lagrange-Labs/reckle-trees/blob/main/LICENSE.pdf).

### Acknowledgements
Special thanks to [Nicolas Gailly](https://github.com/nikkolasg) and the Lagrange Engineering team for their support with this work.
