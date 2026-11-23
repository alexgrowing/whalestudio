import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsAlgebraicPointOfGroupDeterminant
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow

open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.HV

namespace GlobalTheory

namespace PowerSeriesEvalAlgCl

theorem isIntegral_iff_norm_le_one {l : ℕ} [Fact l.Prime] (y : PadicAlgCl l) :
    IsIntegral ℤ_[l] y ↔ ‖y‖ ≤ 1 := by
  have hm : (minpoly ℚ_[l] y).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral y)
  have key : ‖y‖ ≤ 1 ↔ ∀ n, ‖(minpoly ℚ_[l] y).coeff n‖ ≤ 1 := spectralValue_le_one_iff hm
  rw [key]
  refine ⟨fun h n => ?_, fun h => ?_⟩
  · rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · obtain ⟨q, hq, -, hq'⟩ := lifts_and_degree_eq_and_monic
      ((lifts_iff_coeff_lifts (f := algebraMap ℤ_[l] ℚ_[l]) _).2 fun n => ⟨⟨_, h n⟩, rfl⟩) hm
    refine ⟨q, hq', ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq]
    exact minpoly.aeval ℚ_[l] y

theorem exists_coef_ge_finset {l : ℕ} [Fact l.Prime] (c : Coef l) (s : Finset (PadicAlgCl l))
    (hs : ∀ y ∈ s, IsIntegral ℤ_[l] y) : ∃ c' : Coef l, c.O ≤ c'.O ∧ ∀ y ∈ s, y ∈ c'.O := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨c, le_rfl, by simp⟩
  | insert a s _ ih =>
    obtain ⟨c₁, h₁, h₂⟩ := ih fun y hy => hs y (Finset.mem_insert_of_mem hy)
    obtain ⟨c₂, h₃, h₄⟩ := (coefSup l).2.2.1 c₁ a (hs a (Finset.mem_insert_self _ _))
    refine ⟨c₂, h₁.trans h₃, fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact h₄
    · exact h₃ (h₂ y hy)

end PowerSeriesEvalAlgCl

end GlobalTheory
