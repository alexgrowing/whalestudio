import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntegrandPeriodic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotVolumeNeZeroNeTop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DblVacAtInhabited
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DblApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalSourceActsOnOrientedThetaBySubstitutionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubledLagrangianTermFrameIndependentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelEisensteinDoubledThetaTermsEqLagrangianIntStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWPairProof

open GlobalTheory.RawLift

variable {D : D7}

theorem kernel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om →
    ∃ omh : GA D (GlobalTheory.Doubling.dblSp W) × GA D V →* Module.End ℂ (WO (GlobalTheory.Doubling.dblSp W) V → ℂ),
      IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp W) V 1 χV omh ∧
      ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsThetaFunO ψ (GlobalTheory.Doubling.dblSp W) V (dbl V W f₁ f₂) ∧
        ∀ h, thetaKO omh 1 h (dbl V W f₁ f₂) = thetaKO om h 1 f₁ * star (thetaKO om h 1 f₂) := by
  intro D ψ V W χV χW om hw
  have hS := GlobalTheory.AdjLawPf.adjLaw D ψ hw.std V W
  have hom' := GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ V W χV χW om hw
  have hr : ResEta D 1 (GlobalTheory.Doubling.dblSp W).rank := by
    have := GlobalTheory.Eis.SimplePoleModel.resEta_one_two_mul D W.rank
    convert this using 2
    simp [GlobalTheory.Doubling.dblSp]
    omega
  obtain ⟨omh, homh⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ (GlobalTheory.Doubling.dblSp W) V 1 χV hw.std
    ⟨continuous_const, fun _ => rfl⟩ hw.hecS hr hw.resS
  refine ⟨omh, homh, fun f₁ f₂ h₁ h₂ => ?_⟩
  have TC := GlobalTheory.DoublingTheta.thetaClause D ψ W V χW χV (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint om) omh hom' homh
  obtain ⟨hth, hrest⟩ := TC (GlobalTheory.PairLift.dag V W f₂) (GlobalTheory.PairLift.dag V W f₁) (hS.theta _ h₂) (hS.theta _ h₁)
  refine ⟨hth, fun h => ?_⟩
  have e := (hrest 1 1 h).2
  have dd : ∀ f : WO V W → ℂ, GlobalTheory.PairLift.dag W V (GlobalTheory.PairLift.dag V W f) = f := fun f => by
    funext y; simp only [GlobalTheory.PairLift.dag, hS.invol, Complex.conj_conj]
  have d0 : GlobalTheory.PairLift.adjO V W 0 = 0 := by
    have := hS.add 0 0
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  have k : ∀ f : WO V W → ℂ, thetaKO (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint om) 1 h (GlobalTheory.PairLift.dag V W f) =
      starRingEnd ℂ (thetaKO om h 1 f) := fun f => by
    simp only [thetaKO, GlobalTheory.ConjAdjWeil.conjAdjoint_apply, dd]
    simp only [GlobalTheory.PairLift.dag, d0]
  have i1 : GlobalTheory.Doubling.io W (1, 1) = 1 := map_one _
  rw [i1, k, k, Complex.conj_conj] at e
  simp only [map_one, inv_one, Circle.coe_one, mul_one] at e
  rw [show dbl V W f₁ f₂ = GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta W V (GlobalTheory.PairLift.dag V W f₂) (GlobalTheory.PairLift.dag V W f₁) from rfl, e]
  simp only [Complex.star_def]
  ring

theorem terms : ∀ (D : D7) ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr,
    SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ →
    ∀ (χ : (AE D)ˣ →* Circle) (omh : GA D (GlobalTheory.Doubling.dblSp W) × GA D V →* Module.End ℂ (WO (GlobalTheory.Doubling.dblSp W) V → ℂ)),
      IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp W) V 1 χ omh →
    ∀ (ν : Measure (Mx D V.rank W.rank)) (𝓖' : Set (Mx D V.rank W.rank)), IsCovolOne (ratL V W) ν 𝓖' →
      ∃ e : GlobalTheory.Eis.Cosets (GlobalTheory.Doubling.siegel W) (GQ (GlobalTheory.Doubling.dblSp W)) ≃ Lag W, ∀ q,
        GlobalTheory.Eis.term (GlobalTheory.Doubling.siegel W) (GQ (GlobalTheory.Doubling.dblSp W))
          (GlobalTheory.SiegelFormula.swSection W V ν 𝓖' omh (dbl V W f₁ f₂)) 1 q = lagTerm μ 𝓕 (fr (e q)) f₁ f₂ := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hs f₁ f₂ h₁ h₂ χ omh hω ν 𝓖' hν
  obtain ⟨omh', -, hK⟩ := kernel D ψ V W χV χW om hs.weil
  have hF := (hK f₁ f₂ h₁ h₂).1
  obtain ⟨e, he⟩ := GlobalTheory.T.siegelEisenstein_doubledTheta_terms_eq_lagrangianIntegrals D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hs f₁ f₂ h₁ h₂ ν 𝓖' hν
  refine ⟨e, fun q => ?_⟩
  obtain ⟨C, hC, hq⟩ := he q
  rw [← GlobalTheory.T.doubled_lagrangian_term_frame_independent D ψ V W μ 𝓕 hs.covol hs.weil.std f₁ f₂ h₁ h₂ (e q) C (fr (e q)) hC (hs.frame _), ← hq]
  simp only [GlobalTheory.Eis.term, mul_one, GlobalTheory.SiegelFormula.swSection, GlobalTheory.SiegelFormula.valZero]
  congr 1
  funext y
  exact GlobalTheory.T.rational_source_acts_on_orientedTheta_by_substitution D ψ _ V 1 χ omh hω _ hF _ (q.out : GQ (GlobalTheory.Doubling.dblSp W)).2 _

theorem swPair (hW : GlobalTheory.Published.WeilSiegelFormulaUnitary) (D : D7) : SWPair D := by
  intro ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hs f₁ f₂ h₁ h₂
  rcases Nat.eq_zero_or_pos W.rank with h0 | hr
  · exact Model.swPair_rank_zero hs h0 f₁ f₂
  obtain ⟨omh, hω, hK⟩ := kernel D ψ V W χV χW om hs.weil
  obtain ⟨hF, hθ⟩ := hK f₁ f₂ h₁ h₂
  haveI := hs.haarV
  have hwitt : Formalism.MainNotions.SchurIrreducible.wittIdx V = 0 := by
    rw [GlobalTheory.RallisIP.wittIdx_eq_wittIndex]
    exact GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Per.isAniso_of_posDef hs.sigOK hs.pos)
  obtain ⟨ν, 𝓖', hν⟩ := GlobalTheory.Size.exists_isCovolOne W V
  have P := (hW D W V νV hs.haarV hr (Or.inl hwitt)).2 ψ χV omh hω (dbl V W f₁ f₂) hF
  obtain ⟨-, hconv⟩ := P.2 hs.big ν 𝓖' hν
  obtain ⟨hc, hsum⟩ := hconv 1
  obtain ⟨e, he⟩ := terms D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hs f₁ f₂ h₁ h₂ χV omh hω ν 𝓖' hν
  have H1 := hc.hasSum
  rw [hsum] at H1
  have H2 : HasSum (fun Y : Lag W => lagTerm μ 𝓕 (fr Y) f₁ f₂)
      (⨍ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => thetaKO omh 1 h (dbl V W f₁ f₂)) q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure V νV) := by
    refine e.hasSum_iff.1 ?_
    convert H1 using 1
    funext q
    simp [he]
  have A : (⨍ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => thetaKO omh 1 h (dbl V W f₁ f₂)) q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure V νV) =
      ⨍ h in 𝓗, thetaKO omh 1 h (dbl V W f₁ f₂) ∂νV :=
    GlobalTheory.ThetaMean.thetaMean_eq hω hF hs.fdV 1
  have vol := GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V νV 𝓗 ⟨hs.haarV, hs.fdV⟩
  have hv : ((νV 𝓗).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_ne_zero.2 vol)
  have key : ∫ h in 𝓗, thetaKO om h 1 f₁ * star (thetaKO om h 1 f₂) ∂νV = ((νV 𝓗).toReal : ℂ) *
      (⨍ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => thetaKO omh 1 h (dbl V W f₁ f₂)) q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure V νV) := by
    rw [A, setAverage_eq, Complex.real_smul, Measure.real, Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    simp_rw [hθ]
  rw [key]
  exact H2.mul_left _

end GlobalTheory.SWPairProof

end
