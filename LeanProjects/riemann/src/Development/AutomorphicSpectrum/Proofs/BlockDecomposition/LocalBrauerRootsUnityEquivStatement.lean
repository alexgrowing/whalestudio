import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBrauerRootsUnityEquiv
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_brauer_roots_unity_equiv : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → Nonempty (H2 (muLoc F l r A) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) := by
  first | exact @GlobalTheory.CompanionTheory.LocalInv.nonempty_H2_muLoc_equiv_zmod | exact GlobalTheory.CompanionTheory.LocalInv.nonempty_H2_muLoc_equiv_zmod | (intros; apply GlobalTheory.CompanionTheory.LocalInv.nonempty_H2_muLoc_equiv_zmod <;> assumption)
