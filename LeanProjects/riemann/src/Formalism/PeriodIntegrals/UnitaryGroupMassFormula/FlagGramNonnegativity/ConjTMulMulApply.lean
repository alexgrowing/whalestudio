import Formalism.PeriodIntegrals.FlagGramNonneg

noncomputable section

open Matrix PI.FlagGramNonneg

namespace PI.UnitaryGroupMassFormula.FlagGramNonneg

theorem tau_form {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {N : ℕ} (b : Module.Basis (Fin N) E V) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (v w : V) :
    τ (hT v w) = star (fun n => τ (b.repr v n)) ⬝ᵥ
      (((PI.FlagGramNonneg.gram hT b).map τ) *ᵥ (fun n => τ (b.repr w n))) := by
  conv_lhs => rw [← b.sum_repr v, ← b.sum_repr w]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul,
    map_mul, starRingEnd_apply, hτ, dotProduct, mulVec, Matrix.map_apply, PI.FlagGramNonneg.gram,
    Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem conjT_mul_mul_apply {m n : Type} [Fintype m] (A : Matrix m n ℂ) (B : Matrix m m ℂ) (i j : n) :
    (Aᴴ * B * A) i j = star (fun k => A k i) ⬝ᵥ (B *ᵥ fun k => A k j) := by
  simp only [mul_apply, conjTranspose_apply, dotProduct, mulVec, Pi.star_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

theorem gram_tau {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {N : ℕ} (b : Module.Basis (Fin N) E V) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) {ι : Type} (y : ι → V) (i j : ι) :
    ((Matrix.of fun n k => τ (b.repr (y k) n))ᴴ * ((PI.FlagGramNonneg.gram hT b).map τ) *
      (Matrix.of fun n k => τ (b.repr (y k) n))) i j = τ (hT (y i) (y j)) := by
  rw [conjT_mul_mul_apply, tau_form hT b τ hτ]
  rfl

end PI.UnitaryGroupMassFormula.FlagGramNonneg
