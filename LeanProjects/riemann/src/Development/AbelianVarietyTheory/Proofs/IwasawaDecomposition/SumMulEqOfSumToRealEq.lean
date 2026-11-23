import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone

noncomputable section

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.PolFan

section OfCover

variable {X : Type} [AddCommGroup X]

theorem sum_mul_eq_of_sum_toReal_eq {L ι κ : Type} [AddCommGroup L] [Fintype ι] [Fintype κ]
    {j : L →ₗ[ℤ] LinearMap.BilinForm ℤ X} (hj : Function.Injective j) (ℓ : L →ₗ[ℤ] ℤ) {u : ι → L} {w : κ → L}
    {a : ι → ℝ} {b : κ → ℝ} (h : ∑ i, a i • toReal (j (u i)) = ∑ k, b k • toReal (j (w k))) :
    ∑ i, a i * (ℓ (u i) : ℝ) = ∑ k, b k * (ℓ (w k) : ℝ) := by
  have := sum_mul_eq_zero_of_sum_toReal hj ℓ (β := Sum.elim u w) (c := Sum.elim a (-b)) (by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, h, add_neg_cancel])
  rw [Fintype.sum_sum_type] at this
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
  linarith

theorem toReal_injective : Function.Injective (toReal : LinearMap.BilinForm ℤ X → X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :=
  fun β β' h => LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ h a b
    simp only [toReal_apply] at this
    exact_mod_cast this

end OfCover

end GlobalTheory.PolFan
