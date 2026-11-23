import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DualityForAbsGal

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.LocalInv

theorem nonempty_H2_muLoc_equiv_zmod : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → Nonempty (H2 (muLoc F l r A) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) := by
  intro F Ω _ _ _ _ _ l _ r hr A v hA
  exact (GlobalTheory.CompanionTheory.Hypotheses₂.localTateDuality F Ω l r (ZMod (l ^ r)) A (muLoc F l r A) v hr hA
    (GlobalTheory.TameQuot.contAction_muDec A l r)).1

end GlobalTheory.CompanionTheory.LocalInv
