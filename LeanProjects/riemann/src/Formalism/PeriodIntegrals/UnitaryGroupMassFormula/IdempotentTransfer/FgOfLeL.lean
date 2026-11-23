import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.HarderNarasimhan.FinalCor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.TraceFormulaOfRankDegree
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.CharacteristicPolynomialCompatibility

noncomputable section

namespace PI.Dv.Tr

open PI.Dv Module NumberField

section Conv

variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]

def kap (K : Type) [Field K] [NumberField K] : ℝ := Formalism.HN.logDisc K / (finrank ℚ K : ℝ) - Real.log 2

lemma fg_of_le_L (A : Formalism.BasicNotions.HLat K) (hA : A.Good) (M : Submodule (𝓞 K) A.V) (hM : M ≤ A.L) : M.FG :=
  isNoetherian_submodule.mp (isNoetherian_of_fg_of_noetherian A.L hA.2.1) M hM

lemma degL_eq (A : Formalism.BasicNotions.HLat K) (hA : A.Good) (M : Submodule (𝓞 K) A.V) (hM : M ≤ A.L) :
    degL A M = (2 / (finrank ℚ K : ℝ)) * Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize A.b A.X) M +
      (Formalism.HN.rkK M : ℝ) * kap K := by
  have hpl := Formalism.HN.plLat K A.V A.ι A.b A.X hA.1 M (fg_of_le_L A hA M hM)
  have hq : (finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  unfold degL Formalism.HN.muDef kap
  by_cases h0 : Formalism.HN.rkK M = 0
  · have hMb : M = ⊥ := by
      have hs : Submodule.span K (M : Set A.V) = ⊥ := by
        have : FiniteDimensional K A.V := Module.Finite.of_basis A.b
        exact Submodule.finrank_eq_zero.mp h0
      rw [eq_bot_iff]
      intro x hx
      have : x ∈ Submodule.span K (M : Set A.V) := Submodule.subset_span hx
      rw [hs] at this
      exact (Submodule.mem_bot K).mp this ▸ (Submodule.mem_bot _).mpr rfl
    have hdeg : Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize A.b A.X) M = 0 := by
      rw [hMb]
      unfold Formalism.HN.deg
      have : Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize A.b A.X) (⊥ : Submodule (𝓞 K) A.V) = ⊥ := by
        ext u
        simp [Formalism.HN.zl]
      rw [this]
      unfold Formalism.F.deg
      rw [(Formalism.F.covolBasic _).1, Real.log_one, neg_zero]
    rw [h0, hdeg]
    simp
  · have hrk : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize A.b A.X) M : ℝ) = (finrank ℚ K : ℝ) * (Formalism.HN.rkK M : ℝ) := by
      rw [hpl.2.1]
      push_cast
      ring
    have h0' : (Formalism.HN.rkK M : ℝ) ≠ 0 := by exact_mod_cast h0
    unfold Formalism.HN.slope Formalism.F.slope
    have : (Formalism.F.rk (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize A.b A.X) M) : ℝ) =
        (finrank ℚ K : ℝ) * (Formalism.HN.rkK M : ℝ) := hrk
    rw [this]
    unfold Formalism.HN.deg
    field_simp
    ring

end Conv

end PI.Dv.Tr
