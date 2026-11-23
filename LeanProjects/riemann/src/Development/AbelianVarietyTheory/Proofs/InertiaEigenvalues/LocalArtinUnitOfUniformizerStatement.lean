import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinUnitOfUniformizer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharZeroAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import GroundTheory.LocalFields.ConductorReciprocity
import GroundTheory.LocalFields.LubinTateReciprocity
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_artin_unit_of_uniformizer : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → ∀ (σ : Weil h) (π u : 𝒪[w.adicCompletion E]),
    Irreducible π → (u : w.adicCompletion E) = (a σ : w.adicCompletion E) * (π : w.adicCompletion E) ^ deg σ →
    IsUnit u := by
  first | exact @GlobalTheory.HeckeTate.isUnit_artin_mul_zpow | exact GlobalTheory.HeckeTate.isUnit_artin_mul_zpow | (intros; apply GlobalTheory.HeckeTate.isUnit_artin_mul_zpow <;> assumption)
