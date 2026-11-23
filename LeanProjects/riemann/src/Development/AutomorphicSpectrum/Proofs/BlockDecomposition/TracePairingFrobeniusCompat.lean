import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply

open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobPairing

theorem T_phi_expand {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A]
    {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L]
    (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w))
    {F : W →+* W} (φA : A →+* A) (φC : C₀ →+* C₀) (φL : L →ₛₗ[F] L) (fr : K₀ →+* K₀)
    (φD : K₀ ⊗[W] L →+ K₀ ⊗[W] L) (hD : ∀ x y, φD (x ⊗ₜ y) = fr x ⊗ₜ φL y)
    (pT : A ⊗[W] L →+ A ⊗[W] L) (hT : ∀ a y, pT (a ⊗ₜ y) = φA a ⊗ₜ φL y)
    (hφ : ∀ a, φC (c a) = c (φA a)) (hφk : ∀ x, φC (k x) = k (fr x))
    {m : ℕ} (b : Module.Basis (Fin m) K₀ (K₀ ⊗[W] L)) (f : Module.Dual K₀ (K₀ ⊗[W] L))
    (z : A ⊗[W] L) :
    T c k hk f (pT z) = ∑ s, φC (T c k hk (b.coord s) z) * k (f (φD (b s))) := by
  have hsmul : ∀ (x : K₀) (v : K₀ ⊗[W] L), φD (x • v) = fr x • φD v := by
    intro x v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x' y =>
      rw [TensorProduct.smul_tmul', hD, hD, smul_eq_mul, map_mul, TensorProduct.smul_tmul', smul_eq_mul]
    | add v₁ v₂ h₁ h₂ => rw [smul_add, map_add, map_add, h₁, h₂, smul_add]
  have hTt : ∀ (g : Module.Dual K₀ (K₀ ⊗[W] L)) (a : A) (y : L),
      T c k hk g (a ⊗ₜ y) = c a * k (g (1 ⊗ₜ y)) := fun g a y => rfl
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    rw [hT, hTt]
    simp_rw [hTt, map_mul, hφ, hφk]
    have h1 : (1 : K₀) ⊗ₜ[W] φL y = φD (1 ⊗ₜ y) := by rw [hD, map_one]
    have h2 : φD ((1 : K₀) ⊗ₜ[W] y) = ∑ s, fr (b.coord s (1 ⊗ₜ y)) • φD (b s) := by
      conv_lhs => rw [← b.sum_repr ((1 : K₀) ⊗ₜ[W] y)]
      rw [map_sum]
      simp_rw [hsmul]
      rfl
    rw [h1, h2, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, smul_eq_mul, map_mul]
    ring
  | add z₁ z₂ h₁ h₂ =>
    rw [map_add, map_add, h₁, h₂, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_add, map_add, add_mul]

end GlobalTheory.CompanionTheory.FrobPairing
