import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLevelIffAut
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

noncomputable section
namespace GlobalTheory.SimilTheta
open Matrix

variable {g : ℕ}

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
private lemma exists_column_sum_eq_add_two_mul (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (c : Fin 4) :
    ∃ s : ℤ, ∑ r, al r c = m + 2 * s := by
  have h1 : ∑ r, al r c * al r c = m := by
    have := congrFun (congrFun hal c) c
    simpa [Matrix.mul_apply] using this
  have h2 : Even (∑ r, al r c * (al r c - 1)) := Finset.even_sum _ fun r _ => Int.even_mul_pred_self _
  obtain ⟨s, hs⟩ := h2
  refine ⟨-s, ?_⟩
  have : ∑ r, al r c * (al r c - 1) = ∑ r, al r c * al r c - ∑ r, al r c := by
    simp [mul_sub, Finset.sum_sub_distrib]
  linarith

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
private lemma exists_int_two_mul_dotProduct_of_half_integral {g : ℕ} (a : Fin g → ℂ) (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (k : Fin g → ℤ) :
    ∃ t : ℤ, 2 * (a ⬝ᵥ fun i => (k i : ℂ)) = t := by
  refine ⟨∑ i, if a i = 0 then 0 else k i, ?_⟩
  simp only [dotProduct, Finset.mul_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases ha i with h | h <;> simp [h]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
private lemma sum_intCast_mul_column_eq_of_transpose_mul_eq_smul (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (c c' : Fin 4) :
    ∑ r, (al r c : ℂ) * al r c' = if c = c' then (m : ℂ) else 0 := by
  have := congrFun (congrFun hal c) c'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at this
  split_ifs at this ⊢ with h <;> [skip; skip] <;> exact_mod_cast (by simpa using this)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
private lemma sum_column_smul_add_tors_eq {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (m : ℕ) (hm : 1 ≤ m) (al : Matrix (Fin 4) (Fin 4) ℤ) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ) (c : Fin 4) :
    ∑ r, (al r c : ℂ) • (∑ c', al r c' • y c' + _root_.GlobalTheory.SimilTheta.tors τ al m k n r) = (m : ℂ) • y c + _root_.GlobalTheory.SimilTheta.lat τ (k c) (n c) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  unfold _root_.GlobalTheory.SimilTheta.tors
  simp only [← Int.cast_smul_eq_zsmul ℂ, smul_add, Finset.smul_sum, smul_smul, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun r c' => ((al r c : ℂ) * al r c') • y c')]
  simp only [← Finset.sum_smul, sum_intCast_mul_column_eq_of_transpose_mul_eq_smul m al hal]
  have h2 : ∀ x x_1, (↑(al x c) * ((↑m)⁻¹ * ↑(al x x_1)) : ℂ) = (↑m)⁻¹ * (↑(al x c) * ↑(al x x_1)) := fun _ _ => by ring
  have h3 : ∑ x, ∑ x_1, (↑(al x c) * ((↑m)⁻¹ * ↑(al x x_1)) : ℂ) • _root_.GlobalTheory.SimilTheta.lat τ (k x_1) (n x_1) = _root_.GlobalTheory.SimilTheta.lat τ (k c) (n c) := by
    rw [Finset.sum_comm]
    simp only [h2, ← Finset.sum_smul, ← Finset.mul_sum, sum_intCast_mul_column_eq_of_transpose_mul_eq_smul m al hal]
    simp [mul_ite, inv_mul_cancel₀ hm0]
  rw [h3]
  simp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
private lemma intCast_zsmul_vector {g : ℕ} (α : ℤ) (v : Fin g → ℤ) :
    (fun i => (((α • v) i : ℤ) : ℂ)) = (α : ℂ) • fun i => (v i : ℂ) := by
  ext i; simp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
theorem _root_.GlobalTheory.SimilTheta.aut_similitude_and_mul : ∀ (g m : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ), _root_.GlobalTheory.KeyPow.charHalf g a b → τ.IsSymm → 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → (∀ (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ) (c : Fin 4) (k₀ n₀ : Fin g → ℤ), (∏ r, _root_.GlobalTheory.SimilTheta.aut τ a b (al r c • k₀) (al r c • n₀) (∑ c', al r c' • y c' + _root_.GlobalTheory.SimilTheta.tors τ al m k n r)) * Complex.exp (2 * Real.pi * Complex.I * ((fun i => (n c i : ℂ)) ⬝ᵥ _root_.GlobalTheory.SimilTheta.lat τ k₀ n₀)) = _root_.GlobalTheory.SimilTheta.aut τ a b k₀ n₀ (y c) ^ m) ∧ ∀ (k₀ n₀ : Fin g → ℤ) (z : Fin g → ℂ), _root_.GlobalTheory.SimilTheta.aut τ a b ((m : ℤ) • k₀) ((m : ℤ) • n₀) ((m : ℤ) • z) = _root_.GlobalTheory.SimilTheta.aut τ a b k₀ n₀ z ^ (m ^ 2) := by
  intro g m τ a b al hab hτ hm hal
  refine ⟨fun k n y c k₀ n₀ => ?_, fun k₀ n₀ z => ?_⟩
  · obtain ⟨s, hs⟩ := exists_column_sum_eq_add_two_mul m al hal c
    obtain ⟨ta, hta⟩ := exists_int_two_mul_dotProduct_of_half_integral a hab.1 k₀
    obtain ⟨tb, htb⟩ := exists_int_two_mul_dotProduct_of_half_integral b hab.2 n₀
    have hV := sum_column_smul_add_tors_eq τ m hm al hal k n y c
    unfold _root_.GlobalTheory.SimilTheta.aut
    simp only [intCast_zsmul_vector, smul_dotProduct, dotProduct_smul, mulVec_smul, smul_eq_mul]
    rw [← Complex.exp_sum, ← Complex.exp_add, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
    set K₀ : Fin g → ℂ := fun i => (k₀ i : ℂ)
    set N₀ : Fin g → ℂ := fun i => (n₀ i : ℂ)
    set Kc : Fin g → ℂ := fun i => (k c i : ℂ)
    set Nc : Fin g → ℂ := fun i => (n c i : ℂ)
    have hterm : ∀ x, (2 * ↑Real.pi * Complex.I *
            (((↑(al x c) * a ⬝ᵥ K₀) - ↑(al x c) * b ⬝ᵥ N₀) -
                ↑(al x c) * (↑(al x c) * N₀ ⬝ᵥ τ *ᵥ N₀) / 2 -
              ↑(al x c) * N₀ ⬝ᵥ (∑ c', al x c' • y c' + _root_.GlobalTheory.SimilTheta.tors τ al m k n x)) : ℂ) =
        2 * ↑Real.pi * Complex.I * ((al x c : ℂ) * (a ⬝ᵥ K₀ - b ⬝ᵥ N₀) - (al x c : ℂ) * al x c * (N₀ ⬝ᵥ τ *ᵥ N₀ / 2)
          - N₀ ⬝ᵥ ((al x c : ℂ) • (∑ c', al x c' • y c' + _root_.GlobalTheory.SimilTheta.tors τ al m k n x))) := by
      intro x
      rw [dotProduct_smul, smul_eq_mul]
      ring
    simp only [hterm]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      ← dotProduct_sum, hV, sum_intCast_mul_column_eq_of_transpose_mul_eq_smul m al hal c c, if_pos rfl]
    have hs' : ∑ x, (al x c : ℂ) = m + 2 * s := by exact_mod_cast hs
    rw [hs']
    have hsym : Nc ⬝ᵥ τ *ᵥ N₀ = N₀ ⬝ᵥ τ *ᵥ Nc := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hτ.eq, dotProduct_comm]
    have hNK : Nc ⬝ᵥ K₀ = ((n c ⬝ᵥ k₀ : ℤ) : ℂ) := by simp [Nc, K₀, dotProduct]
    have hNK' : N₀ ⬝ᵥ Kc = ((n₀ ⬝ᵥ k c : ℤ) : ℂ) := by simp [N₀, Kc, dotProduct]
    unfold _root_.GlobalTheory.SimilTheta.lat
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    refine ⟨s * (ta - tb) + (n c ⬝ᵥ k₀ - n₀ ⬝ᵥ k c), ?_⟩
    push_cast
    rw [← hNK, ← hNK', ← hta, ← htb]
    linear_combination (2 * ↑Real.pi * Complex.I) * hsym
  · obtain ⟨ta, hta⟩ := exists_int_two_mul_dotProduct_of_half_integral a hab.1 k₀
    obtain ⟨tb, htb⟩ := exists_int_two_mul_dotProduct_of_half_integral b hab.2 n₀
    unfold _root_.GlobalTheory.SimilTheta.aut
    simp only [intCast_zsmul_vector, smul_dotProduct, dotProduct_smul, mulVec_smul, smul_eq_mul]
    rw [← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
    obtain ⟨u, hu⟩ := Int.even_mul_pred_self (m : ℤ)
    have hmu : (m : ℂ) * (m - 1) = u + u := by exact_mod_cast hu
    refine ⟨-u * (ta - tb), ?_⟩
    simp only [zsmul_eq_mul, Int.cast_natCast]
    push_cast
    rw [← hta, ← htb]
    linear_combination (-(2 * ↑Real.pi * Complex.I) * ((a ⬝ᵥ fun i ↦ (k₀ i : ℂ)) - b ⬝ᵥ fun i ↦ (n₀ i : ℂ))) * hmu

end GlobalTheory.SimilTheta
end
