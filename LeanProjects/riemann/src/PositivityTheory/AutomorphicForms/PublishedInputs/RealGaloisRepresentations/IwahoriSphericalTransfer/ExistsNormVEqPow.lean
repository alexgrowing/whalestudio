import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.IsomorphismOfFrobeniusTraces
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AttUniq

theorem exists_normV_eq_pow (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (w : HeightOneSpectrum (𝓞 L)) : ∃ f : ℕ, normV w = normV (w.under (𝓞 F)) ^ f := by
  haveI := w.isMaximal
  refine ⟨w.asIdeal.inertiaDeg (𝓞 F), ?_⟩
  have h := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal (w.under (𝓞 F)).asIdeal (w.under (𝓞 F)).isPrime
      (w.under (𝓞 F)).ne_bot
  rw [Ideal.inertiaDeg'_eq_inertiaDeg] at h
  simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h

theorem main_of_isoOfFrob (hI : IsoOfFrob) : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r r' : G K Ω →* GL (Fin a) (Qbar l)), Continuous r → Continuous r' → IsSSRep r → IsSSRep r' → AttRes π ι K r → AttRes π ι K r' → RepIso r r' := by
  intro F Ω _ _ _ _ _ _ K _ _ _ _ _ _ l _ ι a π r r' hc hc' hs hs' h h'
  refine hI K Ω l ι a r r' hc hc' hs hs' ?_
  filter_upwards [h, h'] with w hw hw'
  obtain ⟨f, hf⟩ := exists_normV_eq_pow F K w
  obtain ⟨B, hB, hr⟩ := hw f hf
  obtain ⟨B', hB', hr'⟩ := hw' f hf
  obtain rfl := hB.unique hB'
  exact ⟨_, hr, hr'⟩

end GlobalTheory.AttUniq

theorem GlobalTheory.AttUniq.attRes_repIso : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r r' : G K Ω →* GL (Fin a) (Qbar l)), Continuous r → Continuous r' → IsSSRep r → IsSSRep r' → AttRes π ι K r → AttRes π ι K r' → RepIso r r' :=
  GlobalTheory.AttUniq.main_of_isoOfFrob GlobalTheory.T.isomorphism_of_frobenius_traces
