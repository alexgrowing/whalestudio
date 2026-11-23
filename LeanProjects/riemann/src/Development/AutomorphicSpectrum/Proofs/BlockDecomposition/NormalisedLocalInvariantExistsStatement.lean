import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalisedLocalInvariantExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalised_local_invariant_exists : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∃ f : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r), Function.Bijective f ∧ IsNormalised ζ A v f := by
  first | exact @GlobalTheory.CompanionTheory.LocalInvariant.exists_bijective_isNormalised | exact GlobalTheory.CompanionTheory.LocalInvariant.exists_bijective_isNormalised | (intros; apply GlobalTheory.CompanionTheory.LocalInvariant.exists_bijective_isNormalised <;> assumption)
