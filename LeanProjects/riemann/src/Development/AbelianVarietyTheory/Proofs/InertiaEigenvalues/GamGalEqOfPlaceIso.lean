import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsOrbitProd
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SupercuspidalLanglands
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemContraIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HasGammaX
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportIrrGLBijectiveDegreeCharZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.FunExt GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RSGam.Transport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
  {φ : Ω ≃+* Ω'}

theorem wdRel_mk (c : Weil h ≃* Weil h') (hcr : ∀ σ σ', WeilRel φ σ σ' ↔ c σ = σ')
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : WDRep h V) (b' : WDRep h' V)
    (hN : b.N = b'.N) (hρ : ∀ σ, b'.ρ (c σ) = b.ρ σ) : WDRel φ (WD.mk b) (WD.mk b') := by
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := (Module.finBasis ℂ V).equivFun
  refine ⟨_, b.transport e, b'.transport e, WD.sound (b.iso_transport e).symm,
    WD.sound (b'.iso_transport e).symm, ?_, fun σ σ' hσ => ?_⟩
  · show e.conjAlgEquiv ℂ b.N = e.conjAlgEquiv ℂ b'.N
    rw [hN]
  · show e.conjAlgEquiv ℂ (b.ρ σ) = e.conjAlgEquiv ℂ (b'.ρ σ')
    rw [← (hcr σ σ').1 hσ, hρ]

theorem wdRel_lpUnr (c : Weil h ≃* Weil h') (hcr : ∀ σ σ', WeilRel φ σ σ' ↔ c σ = σ')
    (hdeg : ∀ σ, deg (c σ) = deg σ) (m : Multiset ℂ) : WDRel φ (WD.lpUnr h m) (WD.lpUnr h' m) := by
  classical
  unfold WD.lpUnr
  refine wdRel_mk c hcr _ _ rfl fun σ => ?_
  rw [WDRep.diag_ρ, WDRep.diag_ρ, hdeg]

end GlobalTheory.RSGam.Transport

end
