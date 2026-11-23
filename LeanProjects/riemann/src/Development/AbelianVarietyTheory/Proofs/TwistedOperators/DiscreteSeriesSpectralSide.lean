import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesTestFunctionTraceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceIntegratedOpMulEqZeroOfIsotypicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOperatorSplitOneRealPlaceStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

namespace GlobalTheory

theorem isIsotypic_of_uEquiv_left {G X Y K : Type} [Group G] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {δ : G →* (X →L[ℂ] X)} {δ' : G →* (Y →L[ℂ] Y)} {ρ : G →* (K →L[ℂ] K)}
    (e : ∃ A : X ≃ₗᵢ[ℂ] Y, ∀ g x, A (δ g x) = δ' g (A x)) (h : IsIsotypic δ ρ) : IsIsotypic δ' ρ := by
  obtain ⟨A, hA⟩ := e
  refine eq_top_iff.2 (h.ge.trans (isoPart_le (Submodule.isClosed_topologicalClosure _) fun T hT x => ?_))
  have hs : ∀ g y, A.symm (δ' g y) = δ g (A.symm y) := fun g y => by
    apply A.injective
    rw [hA g, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  have hx : T x = (T ∘L (A.symm : Y →L[ℂ] X)) (A x) := by simp
  rw [hx]
  refine apply_mem_isoPart (mem_homIn_top.2 fun g y => ?_) _
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [hs]
  exact (mem_homIn_top.1 hT) g _

theorem hasDSComp_of_trace_ne_zero : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → HasDSComp M π := by
  intro hDS hFl hHC hPC D V lam S M T U μa μf μ _ _ fa ff hTD H _ _ _ π hπ c hc hc0 τ
  obtain ⟨δ, hδ⟩ := hFl.exists_hasCompPl (isCMExt_host D) (isHermND_gram (V := V)) hπ (.inl (placeOf D τ))
  have hδ' : IsIsotypic (G := GArch D.sp.cm.sig V.gram (placeOf D τ)) δ.π
      (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) := hδ
  obtain ⟨c', hc', himp⟩ := GlobalTheory.T.discrete_series_test_function_trace hDS hHC hPC D V lam S M T U μa μf μ fa ff hTD τ δ.H δ.π δ.isIrr
  by_cases hc'0 : c' = 0
  · exfalso
    have hRP : IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ := hTD.2.2.2.2.1
    have hmem : ∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w := hTD.2.2.2.2.2.1.mem
    have hfin : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := hTD.2.2.2.2.2.2.isFinFamily
    obtain ⟨Q, hQ, hrep⟩ := GlobalTheory.T.pureTensorOperator_split_oneRealPlace D V μa μf μ hRP fa ff hmem hfin H π hπ.unitary (placeOf D τ)
    haveI : (μa (placeOf D τ)).IsHaarMeasure := hRP.1 _
    have hint : Integrable (fa (placeOf D τ)) (μa (placeOf D τ)) :=
      (continuous_of_mem_ccSmooth (continuous_archCoord _ _ _) (hmem _)).integrable_of_hasCompactSupport (hmem _).1
    have hπw : IsUnitaryRep (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) :=
      isUnitaryRep_comp hπ.unitary (continuous_embArch _ _ _)
    have htc : IsTraceClass (repOp (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) (μa (placeOf D τ)) (fa (placeOf D τ)) * Q) := hrep ▸ hc.1
    let δw : GArch D.sp.cm.sig V.gram (placeOf D τ) →* (δ.H →L[ℂ] δ.H) := δ.π
    have hδirr : IsIrrUnitary δw := δ.isIrr
    have hδw : IsIsotypic δw (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) := hδ'
    have hc'w : HasTrace (repOp δw (μa (placeOf D τ)) (fa (placeOf D τ))) 0 := hc'0 ▸ hc'
    have h0 := GlobalTheory.T.trace_integratedOp_mul_eq_zero_of_isotypic (GArch D.sp.cm.sig V.gram (placeOf D τ)) _ _ hint δ.H H δw _ hδirr hπw hδw Q hQ hc'w htc
    exact hc0 (hc.2.symm.trans (hrep ▸ h0))
  · show IsIsotypic (dsRep M τ) (π.comp (embW V (placeOf D τ)))
    exact isIsotypic_of_uEquiv_left (G := GArch D.sp.cm.sig V.gram (placeOf D τ)) (himp hc'0) hδ'

end GlobalTheory
