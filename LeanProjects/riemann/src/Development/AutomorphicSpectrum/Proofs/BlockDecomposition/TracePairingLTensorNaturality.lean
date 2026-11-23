import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply

open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobPsi

theorem T_lTensor {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A]
    {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L]
    (c : A →+* C₀) (k : K₀ →+* C₀)
    (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w))
    {L' : Type 1} [AddCommGroup L'] [Module W L'] (g : L' →ₗ[W] L)
    (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L') :
    T c k hk f (LinearMap.lTensor A g z) = T c k hk (f ∘ₗ g.baseChange K₀) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a y =>
    rw [LinearMap.lTensor_tmul, T_tmul, T_tmul, LinearMap.comp_apply, LinearMap.baseChange_tmul]
  | add z z' hz hz' => simp only [map_add, hz, hz']

end GlobalTheory.CompanionTheory.FrobPsi
