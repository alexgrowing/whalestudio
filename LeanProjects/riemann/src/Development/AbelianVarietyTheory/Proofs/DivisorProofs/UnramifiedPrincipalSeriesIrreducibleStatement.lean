import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPrincipalSeriesIrreducible
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
open NumberField IsDedekindDomain
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_principal_series_irreducible : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (τ : GlobalTheory.CuspRep.CuspSub E (1 + 1))
    (w : HeightOneSpectrum (𝓞 E)) (χ₁ χ₂ : (w.adicCompletion E)ˣ →* ℂˣ) (s₁ s₂ : ℝ), GlobalTheory.Published.JacquetShalikaBound →
    GlobalTheory.SplitWeil.IsUnram χ₁ → GlobalTheory.SplitWeil.IsUnram χ₂ → (∀ u, ‖(χ₁ u : ℂ)‖ = 1) → (∀ u, ‖(χ₂ u : ℂ)‖ = 1) →
    1 < |s₁ - s₂| →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Q : Representation ℂ (GL (Fin (1 + 1)) (w.adicCompletion E)) V),
      GlobalTheory.SmGL.IsSubquotient Q (GlobalTheory.SmGL.prod₂
        (GlobalTheory.SmGL.detRep (Fin 1) (χ₁ * GlobalTheory.SmGL.absPow (w.adicCompletion E) (s₁ : ℂ)))
        (GlobalTheory.SmGL.detRep (Fin 1) (χ₂ * GlobalTheory.SmGL.absPow (w.adicCompletion E) (s₂ : ℂ)))) →
      ∀ f : Q.IntertwiningMap (τ.locRep w), f ≠ 0 → False := by
  first | exact @GlobalTheory.JSPrinBound.jsBound_no_map | exact GlobalTheory.JSPrinBound.jsBound_no_map | (intros; apply GlobalTheory.JSPrinBound.jsBound_no_map <;> assumption)
