import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductPermEquiv

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.RgGu.Swap

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option maxHeartbeats 1000000 in

theorem swapProd : GlobalTheory.BZSeg.SwapProd k := by
  intro h N x hd j hj M hd2 hd2' hd' C
  have key := GlobalTheory.CompanionTheory.ReorderRev.prodIrr_swap_adj (k := k) x ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl
    (fun q hq hq' => by
      obtain rfl : q = M := hq.symm.trans hd2
      exact C) hd hd'
  exact key

end GlobalTheory.RgGu.Swap
