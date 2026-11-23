import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinCompatLocalDegreeOneStatement

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem isLocalArtin_transport : GlobalArtinReciprocity → ChevalleyUnits → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (a' : Weil h' →* (w'.adicCompletion E')ˣ), IsLocalArtin h a → IsLocalArtin h' a' → ∀ σ σ', WeilRel φ σ σ' → a' σ' = Units.map i.toRingHom.toMonoidHom (a σ) := by
  intro hG hC E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' φ j i hP a a' ha ha' σ σ' hσ
  obtain ⟨art, hart⟩ := hG E Ω
  obtain ⟨art', hart'⟩ := hG E' Ω'
  let x : (w.adicCompletion E)ˣ := Units.map i.symm.toRingHom.toMonoidHom (a' σ')
  have hx : Units.map i.toRingHom.toMonoidHom x = a' σ' := by
    ext
    simp [x]
  have h1 := GlobalTheory.T.globalArtin_compat_localDegreeOne E Ω A w h E' Ω' A' w' h' φ j i hP art art' hart hart' σ σ' x hσ
    (by rw [hx]; exact ha'.glob art' hart' σ')
  have h2 : x = a σ := GlobalTheory.T.globalArtin_localIdele_injective hC E Ω art hart w (h1.trans (ha.glob art hart σ).symm)
  rw [← hx, h2]

end GlobalTheory.LocLanglands
