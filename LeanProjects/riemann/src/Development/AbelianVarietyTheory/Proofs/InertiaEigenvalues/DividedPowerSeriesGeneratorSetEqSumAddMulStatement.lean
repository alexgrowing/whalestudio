import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerSeriesGeneratorSetEqSumAddMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CstSApply
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerSeriesGeneratorSet_eq_sum_add_mul : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ SdSet t K e, ∃ (N : ℕ) (v : ℕ → Wq l a), ∃ y ∈ SdSet t K e, F = ∑ n ∈ Finset.range N, cstS t K (v n) * dpS a e n + (l : ZMod a → K⟦X⟧) * y := by
  first | exact @GlobalTheory.CrysPrism.sdSet_eq_sum_add_mul | exact GlobalTheory.CrysPrism.sdSet_eq_sum_add_mul | (intros; apply GlobalTheory.CrysPrism.sdSet_eq_sum_add_mul <;> assumption)
