import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCoefficientExternalProductEqMulOrthogonalSumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalCongruenceRealPointsIntegrationHeightOnStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteUnitaryQuotientCompactFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionIntegrableAndContinuous
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCartanInvOneOfOnb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightFunProperties
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

namespace GlobalTheory.Core.Rk.Exh.LocalConst

variable {D : D7}

theorem continuous_wcoef {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : WRep S T}
    (hom : IsWeilDatumO ψ S T χS χT om) {ν : Measure (WO S T)} {𝓕 : Set (WO S T)} (hν : IsCovolOne (ratL T S) ν 𝓕)
    {Φ₁ Φ₂ : WO S T → ℂ} (h₁ : IsThetaFunO ψ S T Φ₁) (h₂ : IsThetaFunO ψ S T Φ₂) :
    Continuous (wcoef om ν 𝓕 Φ₁ Φ₂) := by
  have hj := GlobalTheory.Unf.jointCont_all D ψ _ _ _ _ om hom Φ₁ h₁
  show Continuous fun g => ∫ w in 𝓕, om (g, 1) Φ₁ w * conj (Φ₂ w) ∂ν
  exact continuous_covolOne_integral hν (fun g w => om (g, 1) Φ₁ w * conj (Φ₂ w))
    ((hj.comp ((continuous_fst.prodMk continuous_const).prodMk continuous_snd)).mul
      (Complex.continuous_conj.comp (h₂.cont.comp continuous_snd)))
    (fun g => GlobalTheory.Size.mul_conj_periodic hom.std (hom.om_pres _ _ h₁) h₂)

theorem continuous_rcoef {θ : InfFam D} {A : HSp D} {cA : CptF A} (hA : HSpace.SigOK A) (hP : HSpace.IsPosDef A)
    {m : Measure (GA D A)} (hm : m.IsHaarMeasure) {u : GA D A → ℂ} (hu : u ∈ A0 θ A cA) :
    Continuous (rcoef m u u) := by
  obtain ⟨⟨K₀, hK₀, hK₀c⟩, X, K, -, hX, hK, hXK⟩ := GlobalTheory.T.definite_unitary_quotient_compact_fundamentalDomain D A hA hP m hm
  have hu' := (Submodule.mem_inf.1 hu).2
  have huc : Continuous u := hu'.1
  have hul : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ A) u := hu'.2.1
  obtain ⟨C, hC⟩ : ∃ C, ∀ g, ‖u g‖ ≤ C := by
    obtain ⟨C, hC⟩ := hK₀.exists_bound_of_continuousOn huc.continuousOn
    refine ⟨C, fun g => ?_⟩
    obtain ⟨γ, hγ, hg⟩ := hK₀c g
    rw [← hul γ hγ g]
    exact hC _ hg
  have e : ∀ g, rcoef m u u g = ∫ x in X, u (x * g) * conj (u x) ∂m := fun g =>
    GlobalTheory.AutomorphicL2Unitary.pet_eq hX (fun γ hγ x => by simp only [rTr, mul_assoc]; exact hul γ hγ _) hul
  have hfin : m X < ⊤ := (measure_mono hXK).trans_lt hK.measure_lt_top
  rw [show rcoef m u u = fun g => ∫ x in X, u (x * g) * conj (u x) ∂m from funext e]
  refine continuous_of_dominated (bound := fun _ => C * C) (fun g => ?_) (fun g => ?_) ?_ ?_
  · exact ((huc.comp (continuous_id.mul continuous_const)).mul
      (Complex.continuous_conj.comp huc)).aestronglyMeasurable
  · exact .of_forall fun x => by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hC _) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hC x))
  · have : IsFiniteMeasure (m.restrict X) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
    exact integrable_const _
  · exact .of_forall fun x => (huc.comp (continuous_const.mul continuous_id)).mul continuous_const

theorem wcoef_mul_fix {S T : HSp D} (om : WRep S T) (ν : Measure (WO S T)) (𝓕 : Set (WO S T)) (Φ₁ Φ₂ : WO S T → ℂ)
    (x κ : GA D S) (h : om (κ, 1) Φ₁ = Φ₁) : wcoef om ν 𝓕 Φ₁ Φ₂ (x * κ) = wcoef om ν 𝓕 Φ₁ Φ₂ x := by
  have e : ((x * κ, 1) : GA D S × GA D T) = (x, 1) * (κ, 1) := by simp
  simp only [wcoef, e, map_mul, Module.End.mul_apply, h]

theorem rcoef_mul_fix {A : HSp D} (m : Measure (GA D A)) (u : GA D A → ℂ) (x κ : GA D A) (h : ∀ g, u (g * κ) = u g) :
    rcoef m u u (x * κ) = rcoef m u u x := by
  have e : rTr A (x * κ) u = rTr A x u := funext fun g => by simp only [rTr, ← mul_assoc, h]
  simp only [rcoef, e]

end GlobalTheory.Core.Rk.Exh.LocalConst

namespace GlobalTheory.Core.Rk.Exh.LocalConst

theorem integral_const : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (B W H : HSp D) (o : OrthDec B W H) (χA χW : (AE D)ˣ →* Circle) (omB : WRep A B) (omW : WRep A W) (omH : WRep A H), IsWeilDatumO ψ A B χA χW omB → IsWeilDatumO ψ A W χA χW omW → IsWeilDatumO ψ A H χA 1 omH → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u ∈ A0 θ A cA, (∀ κ ∈ prin A β Z, ∀ g, u (g * κ) = u g) → ∀ (sW : RealMat W) (Φ : WO A W → ℂ), Occ ψ θ sW omW m β Z u Φ → ∀ f, IsThetaFunO ψ A H f → f ≠ 0 → (∀ κ ∈ prin A β Z, omH (κ, 1) f = f) → (∀ b ∈ GinfC A, omH (b, 1) f = f) → (∀ ν 𝓕, IsCovolOne (ratL H A) ν 𝓕 → ∀ g ∈ openOff A (frameLat A) (under Z), g ∉ prinInf A β Z → wcoef omH ν 𝓕 f f g = 0) → ∀ νB 𝓕B, IsCovolOne (ratL B A) νB 𝓕B → ∃ C : ℂ, C ≠ 0 ∧ ∀ s : ℂ, ∫ g in openOff A (frameLat A) (under Z), integrand omB m νB 𝓕B (frameLat A) a (o.boxT A Φ f) (o.boxT A Φ f) u u s g ∂m = C := by
  intro D ψ θ A cA a hD B W H o χA χW omB omW omH hB hW hH β Z hZ m hm u hu hufix sW Φ hOcc f hf hf0 hfκ hfb hoff
    νB 𝓕B hνB
  obtain ⟨νW, 𝓕W, hνW⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank A.rank
  obtain ⟨νH, 𝓕H, hνH⟩ := GlobalTheory.MixModel.exists_isCovolOne D H.rank A.rank
  have hΦ : IsThetaFunO ψ A W Φ := hOcc.fock.1
  obtain ⟨hPm, hPsub, hPh, mR, hmR, hint⟩ := GlobalTheory.T.principalCongruence_realPoints_integration_heightOne D θ A cA a hD β Z hZ.frame m hm
  set F : GA D A → ℂ := fun g => wcoef omW νW 𝓕W Φ Φ g * wcoef omH νH 𝓕H f f g * rcoef m u u g with hFdef
  have hFc : Continuous F := ((continuous_wcoef hW hνW hΦ hΦ).mul (continuous_wcoef hH hνH hf hf)).mul
    (continuous_rcoef hD.sig hD.pos hm hu)
  have hbox := GlobalTheory.T.weilCoefficient_externalProduct_eq_mul_orthogonalSum D ψ A B W H o χA χW omB omW omH hB hW hH νB 𝓕B νW 𝓕W νH 𝓕H hνB hνW hνH Φ f hΦ hf
  have hFκ : ∀ (b : GinfC A), ∀ κ ∈ prin A β Z, F ((b : GA D A) * κ) = F b := fun b κ hκ => by
    simp only [hFdef, wcoef_mul_fix omW νW 𝓕W Φ Φ _ κ (hOcc.fix κ hκ), wcoef_mul_fix omH νH 𝓕H f f _ κ (hfκ κ hκ),
      rcoef_mul_fix m u _ κ (hufix κ hκ)]
  set c : ℂ := GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip A H νH 𝓕H f f with hc
  have hc0 : c ≠ 0 := by
    have h := GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hH.std hf hf0 hνH
    have e : c = GlobalTheory.RawLift.thetaIP νH 𝓕H f f := by
      simp only [hc, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip, GlobalTheory.RawLift.thetaIP, mul_comm (f _), Complex.star_def]
    rwa [e]
  have hFb : ∀ b : GinfC A, F b = c * (wcoef omW νW 𝓕W Φ Φ b * rcoef m u u b) := fun b => by
    have e : wcoef omH νH 𝓕H f f b = c := by simp only [wcoef, hfb b b.2, hc]
    simp only [hFdef, e]
    ring
  refine ⟨c * ∫ b : GinfC A, wcoef omW νW 𝓕W Φ Φ b * rcoef m u u b ∂mR, mul_ne_zero hc0 (hOcc.real νW 𝓕W hνW mR hmR),
    fun s => ?_⟩
  have hOm : MeasurableSet (openOff A (frameLat A) (under Z)) :=
    (isOpen_openOff A _ (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) _).measurableSet
  have h1 : ∫ g in openOff A (frameLat A) (under Z), integrand omB m νB 𝓕B (frameLat A) a (o.boxT A Φ f) (o.boxT A Φ f)
      u u s g ∂m = ∫ g in openOff A (frameLat A) (under Z), (prinInf A β Z).indicator F g ∂m := by
    refine setIntegral_congr_fun hOm fun g hg => ?_
    by_cases hgP : g ∈ prinInf A β Z
    · rw [Set.indicator_of_mem hgP]
      simp only [integrand, hbox g, hPh g hgP, one_npow, mul_one, hFdef]
    · rw [Set.indicator_of_notMem hgP]
      simp only [integrand, hbox g, hoff νH 𝓕H hνH g hg hgP, mul_zero, zero_mul]
  rw [h1, setIntegral_indicator hPm, Set.inter_eq_right.2 hPsub, hint F hFc hFκ]
  simp only [hFb]
  exact integral_const_mul c _

end GlobalTheory.Core.Rk.Exh.LocalConst
