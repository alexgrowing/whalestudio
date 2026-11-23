import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastBasicPropertiesStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.ArithThreeInert

theorem main : ∀ [Fact (Nat.Prime 3)] (lam : algebraicClosure ℚ ℂ →+* ℂ_[3]) (d : ℕ) (w σ p : ℂ), d % 3 = 1 → w ^ 2 = -(d : ℂ) → Sz 3 lam 0 (((1 + w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) → Sz 3 lam 0 (((1 - w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 - w) ^ 2 - 1) * p) → Sz 3 lam 0 σ := by
  intro _ lam d w σ p hd hw h1 h2
  obtain ⟨hint, hadd, hmul, -, hneg, -, -⟩ := GlobalTheory.T.algebraicValuationAtLeast_basic_properties 3 lam
  have hsub : ∀ x y : ℂ, Sz 3 lam 0 x → Sz 3 lam 0 y → Sz 3 lam 0 (x - y) := by
    intro x y hx hy
    rw [sub_eq_add_neg]; exact hadd 0 x (-y) hx (hneg 0 y hy)
  have hI : ∀ x : ℂ, IsIntegral ℤ x → Sz 3 lam 0 x := by
    intro x hx
    exact hint 1 x (by norm_num) (by simpa using hx)
  have hw_int : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), ?_, ?_⟩
    · exact Polynomial.Monic.def.mpr (by
        rw [Polynomial.leadingCoeff_X_pow_add_C (by norm_num)])
    · simp [hw]
  have hA : Sz 3 lam 0 ((1 + w) ^ 2 - 1) :=
    hI _ (((isIntegral_one.add hw_int).pow 2).sub isIntegral_one)
  have hB : Sz 3 lam 0 ((1 - w) ^ 2 - 1) :=
    hI _ (((isIntegral_one.sub hw_int).pow 2).sub isIntegral_one)
  have hW : Sz 3 lam 0 w := hI _ hw_int
  have hcomb : Sz 3 lam 0 (((((1 - w) ^ 2 - 1) *
      (((1 + w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p)) -
      (((1 + w) ^ 2 - 1) * (((1 - w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 - w) ^ 2 - 1) * p))) * w) := by
    have := hmul 0 0 _ _ (hsub _ _ (by simpa using hmul 0 0 _ _ hB h1) (by simpa using hmul 0 0 _ _ hA h2)) hW
    simpa using this
  have heq : ((((1 - w) ^ 2 - 1) *
      (((1 + w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p)) -
      (((1 + w) ^ 2 - 1) * (((1 - w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 - w) ^ 2 - 1) * p))) * w
      = ((4 * d ^ 2 : ℕ) : ℂ) * (-σ) := by
    push_cast
    linear_combination (4 * (d : ℂ) * σ) * hw
  rw [heq] at hcomb
  have hd0 : ((4 * d ^ 2 : ℕ) : ℂ) ≠ 0 := by
    have : d ≠ 0 := by rintro rfl; simp at hd
    exact_mod_cast (by positivity : 0 < 4 * d ^ 2).ne'
  have h3 : ¬ 3 ∣ 4 * d ^ 2 := by
    intro h
    have h0 : (4 * d ^ 2) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    rw [Nat.mul_mod, Nat.pow_mod, hd] at h0
    norm_num at h0
  have hinv : Sz 3 lam 0 (((4 * d ^ 2 : ℕ) : ℂ))⁻¹ :=
    hint (4 * d ^ 2) _ h3 (by rw [mul_inv_cancel₀ hd0]; exact isIntegral_one)
  have hm := hmul 0 0 _ _ hinv hcomb
  rw [zero_add] at hm
  have hfin := hneg 0 _ hm
  rw [← mul_assoc, inv_mul_cancel₀ hd0, one_mul, neg_neg] at hfin
  exact hfin

end GlobalTheory.ArithThreeInert
