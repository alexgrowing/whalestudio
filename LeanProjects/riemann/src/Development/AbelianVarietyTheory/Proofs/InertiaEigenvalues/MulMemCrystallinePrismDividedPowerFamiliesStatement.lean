import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulMemCrystallinePrismDividedPowerFamilies
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_mem_crystallinePrismDividedPowerFamilies : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e := by
  first | exact @GlobalTheory.CrysPrism.mul_mem_QSet_of_mem | exact GlobalTheory.CrysPrism.mul_mem_QSet_of_mem | (intros; apply GlobalTheory.CrysPrism.mul_mem_QSet_of_mem <;> assumption)
