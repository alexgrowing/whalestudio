import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonodromyEqLeadingCoeffBreuilKisinDescent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monodromy_eq_leadingCoeff_breuilKisinDescent : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (U : Finset ℤ) (N : ℕ), D.jumps ⊆ U → U ⊆ Finset.Icc (-(η : ℤ)) H → U.card ≤ N + 1 → 1 ≤ η → η < H → 14 * H + (N + 2) * η < l → 10 * H + 2 ≤ l → IsAdicComplete (Ideal.span {(l : O)}) D.Y' → IsHausdorff (Ideal.span {(l : O)}) D.Z → ∀ y ∈ D.Y', ∃ y₀ ∈ D.Y', D.Mon y₀ = D.Lc (D.cls y) := by
  first | exact @GlobalTheory.Proof.exists_monodromy_eq_leadingCoeff_breuilKisinDescent.exists_Mon_eq_Lc_cls | exact GlobalTheory.Proof.exists_monodromy_eq_leadingCoeff_breuilKisinDescent.exists_Mon_eq_Lc_cls | (intros; apply GlobalTheory.Proof.exists_monodromy_eq_leadingCoeff_breuilKisinDescent.exists_Mon_eq_Lc_cls <;> assumption)
