use diol::Result;
use diol::prelude::*;

fn alloc_zero(bencher: Bencher, PlotArg(n): PlotArg) {
	bencher.bench(|| aligned_vec::avec_rt![[64] | 0f64; n]);
}

fn alloc_nonzero(bencher: Bencher, PlotArg(n): PlotArg) {
	bencher.bench(|| aligned_vec::avec_rt![[64] | 1f64; n]);
}

fn main() -> Result<()> {
	let bench = Bench::from_args()?;

	bench.register_many("alloc", list![alloc_zero, alloc_nonzero], (4..25).map(|i| PlotArg(1 << i)));
	bench.run()?;

	Ok(())
}
