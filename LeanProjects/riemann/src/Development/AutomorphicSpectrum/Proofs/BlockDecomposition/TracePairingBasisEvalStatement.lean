import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingBasisEval
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply
open TensorProduct CrystallineSemistableComparison.Pb.Psi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pairing_basis_eval : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ {B : Type} [Field B] (ι : C₀ →+* B) (i : A →+* B), (∀ a, ι (c a) = i a) → ∀ (h : L →+ B), (∀ (w : W) y, h (w • y) = i (algebraMap W A w) * h y) → ∀ {m : ℕ} (b : Module.Basis (Fin m) K₀ (K₀ ⊗[W] L)), ∃ E : K₀ ⊗[W] L →+ B, (∀ x y, E (x ⊗ₜ y) = ι (k x) * h y) ∧ ∀ G : A ⊗[W] L →+ B, (∀ a y, G (a ⊗ₜ y) = i a * h y) → ∀ z, G z = ∑ s, ι (T c k hk (b.coord s) z) * E (b s) := by
  first | exact @GlobalTheory.CompanionTheory.FrobFac.T_fac | exact GlobalTheory.CompanionTheory.FrobFac.T_fac | (intros; apply GlobalTheory.CompanionTheory.FrobFac.T_fac <;> assumption)
