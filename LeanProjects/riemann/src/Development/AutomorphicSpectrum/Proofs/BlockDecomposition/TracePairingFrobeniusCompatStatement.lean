import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingFrobeniusCompat
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply
open TensorProduct CrystallineSemistableComparison.Pb.Psi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pairing_frobenius_compat : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ {F : W →+* W} (φA : A →+* A) (φC : C₀ →+* C₀) (φL : L →ₛₗ[F] L) (fr : K₀ →+* K₀) (φD : K₀ ⊗[W] L →+ K₀ ⊗[W] L), (∀ x y, φD (x ⊗ₜ y) = fr x ⊗ₜ φL y) → ∀ (pT : A ⊗[W] L →+ A ⊗[W] L), (∀ a y, pT (a ⊗ₜ y) = φA a ⊗ₜ φL y) → (∀ a, φC (c a) = c (φA a)) → (∀ x, φC (k x) = k (fr x)) → ∀ {m : ℕ} (b : Module.Basis (Fin m) K₀ (K₀ ⊗[W] L)) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L), T c k hk f (pT z) = ∑ s, φC (T c k hk (b.coord s) z) * k (f (φD (b s))) := by
  first | exact @GlobalTheory.CompanionTheory.FrobPairing.T_phi_expand | exact GlobalTheory.CompanionTheory.FrobPairing.T_phi_expand | (intros; apply GlobalTheory.CompanionTheory.FrobPairing.T_phi_expand <;> assumption)
