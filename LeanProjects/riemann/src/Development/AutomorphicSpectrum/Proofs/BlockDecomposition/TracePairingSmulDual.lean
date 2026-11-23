import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply

open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobPsi

theorem T_ksmul : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ (x : K₀) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L), T c k hk (x • f) z = k x * T c k hk f z := by
  intro W A C₀ _ _ _ _ K₀ _ _ L _ _ c k hk x f z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    rw [T_tmul, T_tmul, LinearMap.smul_apply, smul_eq_mul, map_mul]
    ring
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', mul_add]

end GlobalTheory.CompanionTheory.FrobPsi
