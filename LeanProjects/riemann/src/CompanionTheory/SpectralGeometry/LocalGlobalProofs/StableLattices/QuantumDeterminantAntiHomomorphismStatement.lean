import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantAntiHomomorphism
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharSub
open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantum_determinant_anti_homomorphism : ∀ {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₗ[ℂ] B), f 1 = 1 → (∀ x y, f (x * y) = f y * f x) → ∀ {m : ℕ} (E : Fin m → Fin m → A), GlRel E → ∀ u : ℂ, qdet (fun a b => f (E b a)) u = f (qdet E u) := by
  first | exact @GlobalTheory.CompanionTheory.RgTransport.qdet_anti | exact GlobalTheory.CompanionTheory.RgTransport.qdet_anti | (intros; apply GlobalTheory.CompanionTheory.RgTransport.qdet_anti <;> assumption)
