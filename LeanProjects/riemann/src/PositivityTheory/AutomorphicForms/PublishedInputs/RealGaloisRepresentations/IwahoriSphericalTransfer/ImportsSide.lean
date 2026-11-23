import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.LocalGlobalCompatibilityComplex
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ExistsPlaceCompletionIso
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.GaloisRepRestrictionLocalCompletion
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsRest
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.RecTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AwayDescent

theorem main : GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (P : CuspSub K a), IsBC π P → ∀ (χ : HChar (maximalRealSubfield K)) (r : G F Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (K →+* Qbar l) → Multiset ℤ), IsGalRepOf P χ ι (r.comp (res F Ω K)) wt HT → ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A v), Dec (F := F) A ≤ (res F Ω K).range → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → (∀ (rc : IrrGL (v.adicCompletion F) → WD h), IsRec h rc → ∀ σ, π.IsLocComp v σ → IsWDOf ι r (rc (algNorm σ))) ∧ ∃ x : WD h, IsWDOf ι r x ∧ (x.lpTw ((wt : ℝ) / 2)).tempered := by
  intro L F Ω _ _ _ _ _ _ K _ _ _ _ _ _ _ l _ ι a π P hBC χ r wt HT hG v A h hdec hl
  obtain ⟨w, h', i, hi⟩ := GlobalTheory.T.exists_place_completion_iso F Ω K v A h hdec
  have hlw : ((l : ℕ) : 𝓞 K) ∉ w.asIdeal := by
    intro hw
    apply hl
    have e1 := (h ((l : ℕ) : 𝓞 F))
    have e2 := (h' ((l : ℕ) : 𝓞 K))
    simp only [map_natCast] at e1 e2
    exact e1.1 (e2.2 hw)
  have hL : GlobalTheory.Published.LocalLanglandsGL :=
    GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein L.loc.llc L.loc.conv L.loc.dzc L.loc.dzi
      L.loc.brauer L.loc.chev L.aut.art L.loc.exh L.loc.multi L.loc.cos L.loc.zel L.loc.geo L.loc.bz
  refine ⟨fun rc hrc σ hσ => ?_, ?_⟩
  · obtain ⟨⟨σ', hσ'⟩, -⟩ := GlobalTheory.T.local_global_compatibility_complex L K a P w
    obtain ⟨rc', hrc', -⟩ := hL.1 K Ω A w h'
    obtain ⟨e, he⟩ := hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'
    have hx' := hG.away w hlw A h' rc' hrc' σ' hσ'
    obtain ⟨x, hx, hxx⟩ := GlobalTheory.T.galois_rep_restriction_local_completion F Ω K l ι a r A v w h h' i hi _ hx'
    rwa [← UpperTheory.V.Af.Cq.recTransport hL F K Ω A v w h h' _ i hi a σ σ' e he rc rc' hrc hrc' x hxx]
  · obtain ⟨x', hx', ht⟩ := hG.pure w hlw A h'
    obtain ⟨x, hx, hxx⟩ := GlobalTheory.T.galois_rep_restriction_local_completion F Ω K l ι a r A v w h h' i hi x' hx'
    exact ⟨x, hx, GlobalTheory.TemperedTransport.main F Ω K A v w h h' (algebraMap F K) i hi x x' hxx _ ht⟩

end GlobalTheory.AwayDescent
