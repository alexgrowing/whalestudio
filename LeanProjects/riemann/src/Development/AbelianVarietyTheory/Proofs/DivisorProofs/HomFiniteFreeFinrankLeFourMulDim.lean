import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFreeOfPositiveDefiniteFormBoundedRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeFinrankOfInjectiveModPrimePosDefFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulEqOfTateModuleMapEqSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefQuadraticFormHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDimStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem hom_finite_free_rank_le_of_prime (K : Type) [Field K] (l : ℕ) [Fact l.Prime]
    (hl : (l : K) ≠ 0) (A B : AbVar K) :
    Module.Finite ℤ (A ⟶ B) ∧ Module.Free ℤ (A ⟶ B) ∧
      Module.finrank ℤ (A ⟶ B) ≤ 4 * A.dim * B.dim := by
  obtain ⟨hFA, hfA, hrA, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
  obtain ⟨hFB, hfB, hrB, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl B
  obtain ⟨Q, hpar, hpos, hdef⟩ := GlobalTheory.T.exists_posDef_quadraticForm_hom K A B
  have hrT : Module.finrank ℤ_[l] (Tl l A →ₗ[ℤ_[l]] Tl l B) = 4 * A.dim * B.dim := by
    rw [Module.finrank_linearMap, hrA, hrB]; ring
  refine GlobalTheory.T.finite_free_of_positiveDefinite_form_bounded_rank (A ⟶ B) Q hpar hpos hdef (4 * A.dim * B.dim) ?_
  intro n u hu
  rw [← hrT]
  refine GlobalTheory.T.rank_le_finrank_of_injective_mod_prime_posDef_form l (A ⟶ B) (Tl l A →ₗ[ℤ_[l]] Tl l B) Q hpar hpos hdef (tmap l A B) ?_ n u hu
  intro f φ hφ
  exact GlobalTheory.T.exists_nsmul_eq_of_tateModuleMap_eq_smul K l hl A B f φ hφ

theorem hom_finite_free_rank_le : ∀ (K : Type) [Field K] (A B : AbVar K),
    Module.Finite ℤ (A ⟶ B) ∧ Module.Free ℤ (A ⟶ B) ∧
      Module.finrank ℤ (A ⟶ B) ≤ 4 * A.dim * B.dim := by
  intro K _ A B
  by_cases h2 : ((2 : ℕ) : K) = 0
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : ((3 : ℕ) : K) ≠ 0 := by
      have : ((3 : ℕ) : K) = ((2 : ℕ) : K) + 1 := by push_cast; ring
      rw [this, h2, zero_add]; exact one_ne_zero
    exact hom_finite_free_rank_le_of_prime K 3 h3 A B
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact hom_finite_free_rank_le_of_prime K 2 h2 A B

end GlobalTheory.AV.AbVar

example : ∀ (K : Type) [Field K] (A B : AbVar K), Module.Finite ℤ (A ⟶ B) ∧ Module.Free ℤ (A ⟶ B) ∧ Module.finrank ℤ (A ⟶ B) ≤ 4 * A.dim * B.dim := GlobalTheory.AV.AbVar.hom_finite_free_rank_le
