import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonHeisenbergLevelWeilTransformCompact
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralCompactLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOMapHaar
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section
open scoped ENNReal

namespace GlobalTheory.AvgKill

theorem om_heis_zero {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : WRep S T}
    (hom : IsWeilDatumO ψ S T χS χT om) (q : GA D S × GA D T) (w : WO S T) {h : WO S T → ℂ}
    (hh : IsThetaFunO ψ S T h) : om q (heisO ψ S T w h) 0 = om q h (actO S T q.1 q.2 w) := by
  obtain ⟨g, k⟩ := q
  rw [hom.om_heis g k w h hh]
  simp [heisO, symplOH, symplO, hO]

theorem actO_zero' {D : D7} (S T : HSp D) (g : GA D S) (h : GA D T) : actO S T g h 0 = 0 := by
  simp [actO]

theorem continuous_actO_pair {D : D7} (S T : HSp D) :
    Continuous fun z : (GA D S × GA D T) × WO S T => actO S T z.1.1 z.1.2 z.2 := by
  have h := (GlobalTheory.LevelCompact.continuous_actO_inv S T).comp
    (((continuous_inv.comp (continuous_fst.comp continuous_fst)).prodMk
      (continuous_inv.comp (continuous_snd.comp continuous_fst))).prodMk continuous_snd)
  simpa [Function.comp_def, inv_inv] using h

theorem lintegral_enorm_le_of_sq {α : Type} [MeasurableSpace α] (m : Measure α) (u : α → ℂ)
    (hu : AEStronglyMeasurable u m) (ε : ℝ) (hε : 0 ≤ ε)
    (h2 : ∫⁻ a, ‖u a‖ₑ ^ 2 ∂m ≤ m Set.univ * ENNReal.ofReal ε ^ 2) :
    ∫⁻ a, ‖u a‖ₑ ∂m ≤ m Set.univ * ENNReal.ofReal ε := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hu
  rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)] at h
  simp only [ENNReal.toReal_ofNat, ENNReal.toReal_one, ENNReal.rpow_two] at h
  refine h.trans ?_
  have e : (1 : ℝ) / 1 - 1 / 2 = 1 / 2 := by norm_num
  rw [e]
  calc (∫⁻ a, ‖u a‖ₑ ^ 2 ∂m) ^ (1 / (2 : ℝ)) * m Set.univ ^ (1 / (2 : ℝ))
      ≤ (m Set.univ * ENNReal.ofReal ε ^ 2) ^ (1 / (2 : ℝ)) * m Set.univ ^ (1 / (2 : ℝ)) := by
        gcongr
    _ = m Set.univ * ENNReal.ofReal ε := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        have e2 : (ENNReal.ofReal ε ^ 2) ^ (1 / (2 : ℝ)) = ENNReal.ofReal ε := by
          rw [one_div, ← Nat.cast_ofNat (R := ℝ), ENNReal.pow_rpow_inv_natCast (by norm_num)]
        rw [e2, mul_comm _ (ENNReal.ofReal ε), mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
        norm_num
        ring

theorem integral_om_actO_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsWeilDatumO ψ S T χS χT om → ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasure μ] (p : X → GA D S × GA D T) (c : X → ℂ) (K : Set (GA D S × GA D T)), Continuous p → Continuous c → (∃ C : ℝ, ∀ x, ‖c x‖ ≤ C) → IsCompact K → (∀ᵐ x ∂μ, p x ∈ K) → ∀ f, IsThetaFunO ψ S T f → (∀ w, Integrable (fun x => c x * om (p x) f (actO S T (p x).1 (p x).2 w)) μ) ∧ Continuous (fun w => ∫ x, c x * om (p x) f (actO S T (p x).1 (p x).2 w) ∂μ) := by
  intro D ψ S T χS χT om hom X _ _ _ _ μ _ p c K hp hc hcb hK hpK f hf
  obtain ⟨C, hC⟩ := hcb
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : SecondCountableTopology (WO S T) := i3
  haveI : FirstCountableTopology (WO S T) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  have hG : Continuous fun z : (GA D S × GA D T) × WO S T => om z.1 f (actO S T z.1.1 z.1.2 z.2) :=
    (GlobalTheory.Unf.jointCont_all D ψ S T χS χT om hom f hf).comp (continuous_fst.prodMk (continuous_actO_pair S T))
  have hFc : ∀ w, Continuous fun x => c x * om (p x) f (actO S T (p x).1 (p x).2 w) := fun w =>
    hc.mul (hG.comp (hp.prodMk continuous_const))
  have hloc : ∀ N : Set (WO S T), IsCompact N → ∃ M : ℝ, ∀ w ∈ N, ∀ᵐ x ∂μ,
      ‖c x * om (p x) f (actO S T (p x).1 (p x).2 w)‖ ≤ C * M := by
    intro N hN
    obtain ⟨M, hM⟩ := (hK.prod hN).exists_bound_of_continuousOn hG.continuousOn
    refine ⟨M, fun w hw => hpK.mono fun x hx => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hC x) (hM (p x, w) ⟨hx, hw⟩) (norm_nonneg _) ((norm_nonneg _).trans (hC x))
  refine ⟨fun w => ?_, continuous_iff_continuousAt.2 fun w₀ => ?_⟩
  · obtain ⟨M, hM⟩ := hloc {w} isCompact_singleton
    exact Integrable.of_bound (hFc w).aestronglyMeasurable (C * M) (hM w rfl)
  · obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds w₀
    obtain ⟨M, hM⟩ := hloc N hNc
    exact continuousAt_of_dominated (Filter.Eventually.of_forall fun w => (hFc w).aestronglyMeasurable)
      (Filter.mem_of_superset hN fun w hw => hM w hw) (integrable_const (C * M))
      (Filter.Eventually.of_forall fun x =>
        (continuous_const.mul (hG.comp (continuous_const.prodMk continuous_id))).continuousAt)

theorem lintegral_om_actO_le : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsWeilDatumO ψ S T χS χT om → ∀ (ν : Measure (WO S T)), ν.IsAddHaarMeasure → ∀ (K : Set (GA D S × GA D T)) (N : Set (WO S T)), IsCompact K → IsCompact N → ∃ B : ENNReal, B ≠ ⊤ ∧ ∀ h, IsThetaFunO ψ S T h → ∀ ε : ℝ, (∀ w, ‖h w‖ ≤ ε) → ∀ q ∈ K, ∫⁻ w in N, ‖om q h (actO S T q.1 q.2 w)‖ₑ ∂ν ≤ B * ENNReal.ofReal ε := by
  intro D ψ S T χS χT om hom ν hν K N hK hN
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : LocallyCompactSpace (WO S T) := i2
  haveI : SecondCountableTopology (WO S T) := i3
  haveI : T2Space (WO S T) := i4
  haveI : DiscreteTopology (ratL T S) := i5
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  have := Formalism.IndefR.PHeisFC.countable_ratL T S
  have : MeasurableConstVAdd (ratL T S) (WO S T) := ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  have : VAddInvariantMeasure (ratL T S) (WO S T) ν := ⟨fun c s _ => measure_preimage_add ν (c : WO S T) s⟩
  have hFD : IsAddFundamentalDomain (ratL T S) (Formalism.IndefR.PHeisFC.FD T S) ν :=
    IsAddFundamentalDomain.mk' (Formalism.IndefR.PHeisFC.meas_FD T S).nullMeasurableSet (Formalism.IndefR.PHeisFC.exU T S)
  have hfin : ν (Formalism.IndefR.PHeisFC.FD T S) < ⊤ := (Formalism.IndefR.PHeisFC.finCovol T S).2 ν _ hν hFD
  set K' := (fun z : (GA D S × GA D T) × WO S T => actO S T z.1.1 z.1.2 z.2) '' (K ×ˢ N) with hK'
  have hK'c : IsCompact K' := (hK.prod hN).image (continuous_actO_pair S T)
  obtain ⟨n, hn⟩ := GlobalTheory.ThetaGrowth.lintegral_compact_le (ratL T S) ν hFD hK'c
  refine ⟨n * ν (Formalism.IndefR.PHeisFC.FD T S), ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hfin.ne,
    fun h hh ε hε q hq => ?_⟩
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε 0)
  set H := om q h with hHdef
  have hH : IsThetaFunO ψ S T H := hom.om_pres q h hh
  have hψ : ∀ a, ‖ψ a‖ = 1 := hom.std.1.2.1
  have ha : Measurable (actO S T q.1 q.2) := (continuous_actO_pair S T).comp (continuous_const.prodMk continuous_id) |>.measurable
  have hHm : Measurable fun w => ‖H w‖ₑ := hH.cont.enorm.measurable

  have s1 : ∫⁻ w in N, ‖H (actO S T q.1 q.2 w)‖ₑ ∂ν ≤ ∫⁻ w in K', ‖H w‖ₑ ∂ν := by
    calc ∫⁻ w in N, ‖H (actO S T q.1 q.2 w)‖ₑ ∂ν
        = ∫⁻ w in N, K'.indicator (fun y => ‖H y‖ₑ) (actO S T q.1 q.2 w) ∂ν := by
          refine setLIntegral_congr_fun hN.measurableSet (fun w hw => ?_)
          rw [Set.indicator_of_mem (Set.mem_image_of_mem (fun z : (GA D S × GA D T) × WO S T => actO S T z.1.1 z.1.2 z.2) (Set.mk_mem_prod hq hw))]
      _ ≤ ∫⁻ w, K'.indicator (fun y => ‖H y‖ₑ) (actO S T q.1 q.2 w) ∂ν := setLIntegral_le_lintegral _ _
      _ = ∫⁻ y, K'.indicator (fun y => ‖H y‖ₑ) y ∂(ν.map (actO S T q.1 q.2)) :=
          (lintegral_map (hHm.indicator hK'c.measurableSet) ha).symm
      _ = ∫⁻ y in K', ‖H y‖ₑ ∂ν := by
          rw [GlobalTheory.actO_map_haar D S T q.1 q.2 ν hν, lintegral_indicator hK'c.measurableSet]

  have s2 : ∫⁻ w in K', ‖H w‖ₑ ∂ν ≤ n * ∫⁻ w in Formalism.IndefR.PHeisFC.FD T S, ‖H w‖ₑ ∂ν := by
    refine hn _ hHm (fun γ hγ w => ?_)
    obtain ⟨ξ, rfl⟩ := hγ
    have e := hH.quasi ξ w
    simp only [ratW] at e
    rw [show ((incA D).toAddMonoidHom.mapMatrix ξ : WO S T) = ξ.map (incA D) from rfl, e, enorm_mul]
    rw [← ofReal_norm_eq_enorm (ψ _), hψ, ENNReal.ofReal_one, one_mul]

  have s3 : ∫⁻ w in Formalism.IndefR.PHeisFC.FD T S, ‖H w‖ₑ ∂ν ≤
      ν (Formalism.IndefR.PHeisFC.FD T S) * ENNReal.ofReal ε := by
    have := lintegral_enorm_le_of_sq (ν.restrict (Formalism.IndefR.PHeisFC.FD T S)) H
      hH.cont.aestronglyMeasurable ε hε0 ?_
    · simpa [Measure.restrict_apply_univ] using this
    rw [Measure.restrict_apply_univ, hom.om_unit ν _ hν hFD q h hh]
    calc ∫⁻ w in Formalism.IndefR.PHeisFC.FD T S, ‖h w‖ₑ ^ 2 ∂ν
        ≤ ∫⁻ _w in Formalism.IndefR.PHeisFC.FD T S, ENNReal.ofReal ε ^ 2 ∂ν := by
          refine lintegral_mono fun w => ?_
          gcongr
          rw [← ofReal_norm_eq_enorm]
          exact ENNReal.ofReal_le_ofReal (hε w)
      _ = _ := by rw [setLIntegral_const, mul_comm]
  calc ∫⁻ w in N, ‖om q h (actO S T q.1 q.2 w)‖ₑ ∂ν ≤ n * (ν (Formalism.IndefR.PHeisFC.FD T S) * ENNReal.ofReal ε) :=
        s1.trans (s2.trans (by gcongr))
    _ = _ := by ring

theorem theta_sub' {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (f - g) := by
  obtain ⟨U, hU, hUf⟩ := hf.level
  obtain ⟨U', hU', hUg⟩ := hg.level
  refine ⟨fun γ w => ?_, ⟨U ⊓ U', ?_, fun u hu h0 => ?_⟩, hf.cont.sub hg.cont, fun k L hL hL0 w => ?_⟩
  · simp only [Pi.sub_apply, hf.quasi γ w, hg.quasi γ w, mul_sub]
  · rw [AddSubgroup.coe_inf]; exact hU.inter hU'
  · funext w
    have e1 := congrFun (hUf u hu.1 h0) w
    have e2 := congrFun (hUg u hu.2 h0) w
    simp only [heisO, Pi.sub_apply] at e1 e2 ⊢
    rw [mul_sub, e1, e2]
  · exact (hf.smooth k L hL hL0 w).sub (hg.smooth k L hL hL0 w)

theorem average_kills_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsWeilDatumO ψ S T χS χT om → ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasure μ] (p : X → GA D S × GA D T) (c : X → ℂ) (K : Set (GA D S × GA D T)), Continuous p → Continuous c → (∃ C : ℝ, ∀ x, ‖c x‖ ≤ C) → IsCompact K → (∀ᵐ x ∂μ, p x ∈ K) → ∀ M : Submodule ℂ (WO S T → ℂ), (∀ g ∈ M, IsThetaFunO ψ S T g) → (∀ g ∈ M, ∀ w, heisO ψ S T w g ∈ M) → (∀ g ∈ M, ∫ x, c x * om (p x) g 0 ∂μ = 0) → ∀ f, IsThetaFunO ψ S T f → GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.UnifLimit M f → ∫ x, c x * om (p x) f 0 ∂μ = 0 := by
  intro D ψ S T χS χT om hom X _ _ _ _ μ _ p c K hp hc hcb hK hpK M hMt hMh hM0 f hf hfl
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : LocallyCompactSpace (WO S T) := i2
  haveI : SecondCountableTopology (WO S T) := i3
  haveI : T2Space (WO S T) := i4
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  let ν : Measure (WO S T) := Measure.addHaar
  have hν : ν.IsAddHaarMeasure := by infer_instance
  let F : (WO S T → ℂ) → X → WO S T → ℂ := fun h x w => c x * om (p x) h (actO S T (p x).1 (p x).2 w)
  let Φ : WO S T → ℂ := fun w => ∫ x, F f x w ∂μ
  obtain ⟨hint, hcont⟩ := integral_om_actO_continuous D ψ S T χS χT om hom X μ p c K hp hc hcb hK hpK f hf
  have hΦ0 : ∫ x, c x * om (p x) f 0 ∂μ = Φ 0 := by
    simp only [Φ, F, actO_zero']
  obtain ⟨N, hNc, hN0⟩ := exists_compact_mem_nhds (0 : WO S T)
  obtain ⟨B, hBtop, hB⟩ := lintegral_om_actO_le D ψ S T χS χT om hom ν hν K N hK hNc
  obtain ⟨C, hC⟩ := hcb
  have hgz : ∀ g ∈ M, ∀ w, ∫ x, F g x w ∂μ = 0 := by
    intro g hg w
    rw [← hM0 (heisO ψ S T w g) (hMh g hg w)]
    congr 1; funext x
    simp only [F]
    rw [om_heis_zero hom (p x) w (hMt g hg)]
  have hjc : ∀ h, IsThetaFunO ψ S T h →
      Continuous fun z : WO S T × X => om (p z.2) h (actO S T (p z.2).1 (p z.2).2 z.1) := by
    intro h hh
    have j := GlobalTheory.Unf.jointCont_all D ψ S T χS χT om hom h hh
    exact j.comp ((hp.comp continuous_snd).prodMk
      ((continuous_actO_pair S T).comp ((hp.comp continuous_snd).prodMk continuous_fst)))
  have hbound : ∀ ε : ℝ, 0 < ε →
      ∫⁻ w in N, ‖Φ w‖ₑ ∂ν ≤ ENNReal.ofReal C * μ Set.univ * B * ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨g, hgM, hfg⟩ := hfl ε hε
    have hgt := hMt g hgM
    have hht : IsThetaFunO ψ S T (f - g) := theta_sub' hf hgt
    obtain ⟨hintg, -⟩ := integral_om_actO_continuous D ψ S T χS χT om hom X μ p c K hp hc ⟨C, hC⟩ hK hpK g hgt
    have hΦw : ∀ w, Φ w = ∫ x, F (f - g) x w ∂μ := by
      intro w
      have e : ∀ x, F (f - g) x w = F f x w - F g x w := by
        intro x; simp only [F, map_sub, LinearMap.sub_apply, Pi.sub_apply, mul_sub]
      simp_rw [e]
      rw [integral_sub (hint w) (hintg w), hgz g hgM w, sub_zero]
    let G : WO S T → X → ℝ≥0∞ := fun w x =>
      ENNReal.ofReal C * ‖om (p x) (f - g) (actO S T (p x).1 (p x).2 w)‖ₑ
    have hpt : ∀ w, ‖Φ w‖ₑ ≤ ∫⁻ x, G w x ∂μ := by
      intro w
      rw [hΦw w]
      refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
      simp only [F, G, enorm_mul]
      gcongr
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hC x)
    have hGm : AEMeasurable (Function.uncurry G) ((ν.restrict N).prod μ) := by
      have := (hjc _ hht).enorm
      exact (measurable_const.mul this.measurable).aemeasurable
    calc ∫⁻ w in N, ‖Φ w‖ₑ ∂ν ≤ ∫⁻ w in N, ∫⁻ x, G w x ∂μ ∂ν := lintegral_mono fun w => hpt w
      _ = ∫⁻ x, ∫⁻ w in N, G w x ∂ν ∂μ := lintegral_lintegral_swap hGm
      _ ≤ ∫⁻ _x, ENNReal.ofReal C * (B * ENNReal.ofReal ε) ∂μ := by
        refine lintegral_mono_ae (hpK.mono fun x hx => ?_)
        simp only [G]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        gcongr
        exact hB _ hht ε (fun w => by simpa using (hfg w)) _ hx
      _ = _ := by rw [lintegral_const]; ring
  have hzero : ∫⁻ w in N, ‖Φ w‖ₑ ∂ν = 0 := by
    have hA : ENNReal.ofReal C * μ Set.univ * B ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _)) hBtop
    have hT : Filter.Tendsto (fun δ : ℝ => ENNReal.ofReal C * μ Set.univ * B * ENNReal.ofReal δ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal C * μ Set.univ * B * ENNReal.ofReal 0)) :=
      ENNReal.Tendsto.const_mul ((ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds) (Or.inr hA)
    rw [ENNReal.ofReal_zero, mul_zero] at hT
    exact le_antisymm (ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun δ hδ => hbound δ hδ)) (zero_le)
  have hae : ∀ᵐ w ∂(ν.restrict N), ‖Φ w‖ₑ = 0 :=
    (lintegral_eq_zero_iff' hcont.enorm.measurable.aemeasurable).1 hzero
  rw [hΦ0]
  by_contra hne
  have hU : IsOpen {w | Φ w ≠ 0} := isOpen_ne_fun hcont continuous_const
  have hpos : 0 < ν ({w | Φ w ≠ 0} ∩ interior N) :=
    (hU.inter isOpen_interior).measure_pos ν ⟨0, hne, mem_interior_iff_mem_nhds.2 hN0⟩
  have hnull : ν.restrict N {w | ‖Φ w‖ₑ ≠ 0} = 0 := by
    rw [ae_iff] at hae; simpa using hae
  rw [Measure.restrict_apply' hNc.measurableSet] at hnull
  exact hpos.ne' (measure_mono_null (Set.inter_subset_inter (fun w hw => by simpa using hw) interior_subset) hnull)

end GlobalTheory.AvgKill
