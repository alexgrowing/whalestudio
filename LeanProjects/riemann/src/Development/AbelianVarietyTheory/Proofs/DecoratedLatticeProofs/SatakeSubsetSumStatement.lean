import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeSubsetSum
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_powersetCard_borelParam_eq_genVal : ∀ (q N : ℕ), 0 < q → ∀ (α : Fin N → ℂˣ) (n : ℕ), ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n, ((q : ℂ) ^ ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card * ∏ a ∈ S, borelParam q α a) = genVal q 0 N (Finset.univ.val.map α) n := by
  first | exact @GlobalTheory.SatakeSubsetSum.satake_subset_sum | exact GlobalTheory.SatakeSubsetSum.satake_subset_sum | (intros; apply GlobalTheory.SatakeSubsetSum.satake_subset_sum <;> assumption)
