import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEvalFixedOfFixed
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply
open TensorProduct CrystallineSemistableComparison.Pb.Psi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_eval_fixed_of_fixed : ∀ {W C₀ : Type} [CommRing W] [CommRing C₀] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (k : K₀ →+* C₀) {B : Type} [Field B] [IsFractionRing W K₀] (ι : C₀ →+* B) (σB : B →+* B) (h : L →+ B) (E : K₀ ⊗[W] L →+ B), (∀ x y, E (x ⊗ₜ y) = ι (k x) * h y) → (∀ w, σB (ι (k (algebraMap W K₀ w))) = ι (k (algebraMap W K₀ w))) → (∀ y, σB (h y) = h y) → ∀ v : K₀ ⊗[W] L, σB (E v) = E v := by
  first | exact @GlobalTheory.CompanionTheory.FrobFix.extension_fixed | exact GlobalTheory.CompanionTheory.FrobFix.extension_fixed | (intros; apply GlobalTheory.CompanionTheory.FrobFix.extension_fixed <;> assumption)
