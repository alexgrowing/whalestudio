import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalListedTopForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinCoefMultT
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumNonzeroCuspForm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnMulRight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvari
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageThetaFamilySmooth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergDerivWeilTranslateContinuousCombinatio
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CenAvgOne

open scoped ContDiff

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

def avg1 {K : Type} [MeasurableSpace K] (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (μ : Measure K)
    (j : K → GA D S) (c : K → ℂ) (Φ : WO S T → ℂ) : WO S T → ℂ :=
  fun w => ∫ k, c k * om (j k, 1) Φ w ∂μ

theorem continuous_fam (hom : IsWeilDatumO ψ S T χS χT om) {Φ : WO S T → ℂ} (hΦ : IsThetaFunO ψ S T Φ) {K : Type}
    [TopologicalSpace K] {p : K → GA D S × GA D T} (hp : Continuous p) :
    Continuous fun q : K × WO S T => om (p q.1) Φ q.2 :=
  (GlobalTheory.ThetaJointCont.continuous_om_oriented hom hΦ).comp ((hp.comp continuous_fst).prodMk continuous_snd)

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  [IsFiniteMeasure μ] {j : K → GA D S} {c : K → ℂ} {Φ : WO S T → ℂ}

theorem isThetaFunction_average_compactFamily_weilTranslates (hom : IsWeilDatumO ψ S T χS χT om) (hjc : Continuous j) (hj : ∀ k, j k ∈ GinfC S)
    (hc : Continuous c) (hΦ : IsThetaFunO ψ S T Φ) : IsThetaFunO ψ S T (avg1 om μ j c Φ) := by
  have hψ := hom.std
  have hp : Continuous fun k => (j k, (1 : GA D T)) := hjc.prodMk continuous_const
  refine ⟨fun γ w => ?_, ?_, ?_, ?_⟩
  · simp only [avg1]
    rw [← integral_const_mul]
    congr 1
    funext k
    rw [(hom.om_pres _ _ hΦ).quasi]
    ring
  · obtain ⟨U, hU, h⟩ := hΦ.level
    refine ⟨U, hU, fun u hu hu0 => ?_⟩
    funext w
    simp only [heisO, avg1]
    rw [← integral_const_mul]
    congr 1
    funext k
    have := congrFun (hom.om_heis (j k) 1 u Φ hΦ) w
    rw [h u hu hu0, GlobalTheory.FrComb.actO_real (hj k) (GinfC T).one_mem hu0] at this
    rw [this, heisO]
    ring
  · exact GlobalTheory.AvgFam.continuous_avg μ (F := fun k w => c k * om (j k, 1) Φ w)
      ((hc.comp continuous_fst).mul (continuous_fam hom hΦ hp))
  · let gen : Set (K → WO S T → ℂ) := {F | ∃ (c : K → ℂ) (G : WO S T → ℂ), Continuous c ∧ IsThetaFunO ψ S T G ∧
      F = fun k => c k • om (j k, 1) G}
    have h1 : ∀ F ∈ Submodule.span ℂ gen, Continuous fun q : K × WO S T => F q.1 q.2 := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem F h =>
        obtain ⟨c, G, hc, hG, rfl⟩ := h
        exact (hc.comp continuous_fst).mul (continuous_fam hom hG hp)
      | zero => exact continuous_const
      | add F F' _ _ h h' => exact h.add h'
      | smul a F _ h => exact h.const_smul a
    have h2 : ∀ F ∈ Submodule.span ℂ gen, ∀ k, IsThetaFunO ψ S T (F k) := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem F h =>
        obtain ⟨c, G, hc, hG, rfl⟩ := h
        exact fun k => GlobalTheory.WeilVacMove.isTheta_smul _ (hom.om_pres _ _ hG)
      | zero => exact fun _ => GlobalTheory.WeilVacMove.isTheta_zero
      | add F F' _ _ h h' => exact fun k => GlobalTheory.WeilVacMove.isTheta_add (h k) (h' k)
      | smul a F _ h => exact fun k => GlobalTheory.WeilVacMove.isTheta_smul a (h k)
    have h3 : ∀ F ∈ Submodule.span ℂ gen, ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) →
        (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k)) ∈ Submodule.span ℂ gen := by
      intro F hF M hM hM0
      induction hF using Submodule.span_induction with
      | mem F h =>
        obtain ⟨c, G, hc, hG, rfl⟩ := h
        obtain ⟨m, N, e, hN, hN0, he, hexp⟩ := GlobalTheory.HeisLineComb.dLine_om_comb D ψ S T χS χT om hom M hM hM0
        have key : (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (c k • om (j k, 1) G)) =
            ∑ i, fun k => (c k * e i (j k, 1)) • om (j k, 1) (GlobalTheory.WeilVacMove.dLine ψ S T (N i) G) := by
          funext k
          rw [GlobalTheory.CenAvg.dLine_smul, hexp _ _ hG, Finset.smul_sum, Finset.sum_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul]
        rw [key]
        exact Submodule.sum_mem _ fun i _ => Submodule.subset_span
          ⟨_, _, hc.mul ((he i).comp hp), (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ (hN i) (hN0 i) hG).2, rfl⟩
      | zero =>
        have : (fun k : K => GlobalTheory.WeilVacMove.dLine ψ S T M ((0 : K → WO S T → ℂ) k)) = 0 := by
          funext k x
          simp [GlobalTheory.WeilVacMove.dLine, heisO]
        rw [this]
        exact Submodule.zero_mem _
      | add F F' hF hF' h h' =>
        have : (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M ((F + F') k)) =
            (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k)) + fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F' k) :=
          funext fun k => GlobalTheory.CenAvg.dLine_add hψ hM hM0 (h2 F hF k) (h2 F' hF' k)
        rw [this]
        exact Submodule.add_mem _ h h'
      | smul a F _ h =>
        have : (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M ((a • F) k)) = a • fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k) :=
          funext fun k => GlobalTheory.CenAvg.dLine_smul M a (F k)
        rw [this]
        exact Submodule.smul_mem _ a h
    intro n L hL hL0 w
    have := GlobalTheory.ThetaAvgSmooth.avg_smooth D ψ hψ S T K μ (Submodule.span ℂ gen : Set _) h1 h2 h3 _
      (Submodule.subset_span (show _ ∈ gen from ⟨c, Φ, hc, hΦ, rfl⟩)) n L hL hL0 w
    simpa only [avg1, Pi.smul_apply, smul_eq_mul] using this

theorem weilOperator_average_eq_average_translated [SecondCountableTopology K] [IsTopologicalGroup (GA D S)] [IsTopologicalGroup (GA D T)]
    (hom : IsWeilDatumO ψ S T χS χT om) (hjc : Continuous j) (hj : ∀ k, j k ∈ GinfC S)
    (hc : Continuous c) (hΦ : IsThetaFunO ψ S T Φ) (p : GA D S × GA D T) (x : WO S T) :
    om p (avg1 om μ j c Φ) x = ∫ k, c k * om (p * (j k, 1)) Φ x ∂μ := by
  have hp : Continuous fun k => (j k, (1 : GA D T)) := hjc.prodMk continuous_const
  have hm : ∀ k, om p (om (j k, 1) Φ) = om (p * (j k, 1)) Φ := fun k => by
    rw [map_mul, Module.End.mul_apply]
  have := GlobalTheory.CenAvg.om_integral μ hom hc (F := fun k => om (j k, 1) Φ) p (fun k => hom.om_pres _ _ hΦ)
    (continuous_fam hom hΦ hp) (by simp only [hm]; exact continuous_fam hom hΦ (continuous_const.mul hp))
    (isThetaFunction_average_compactFamily_weilTranslates μ hom hjc hj hc hΦ) x
  simp only [hm] at this
  exact this

end GlobalTheory.CenAvgOne

namespace GlobalTheory.CenAvgOne

theorem exists_central_average_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → S.SigOK → S.IsDefinite → ∀ (ν : Measure (GA D S)) (fd : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) fd ν → ∀ (χ φ : GA D S → ℂ), GlobalTheory.SeeSaw.HasCen S χ φ → GlobalTheory.Unf.IsContAut S φ → ∀ Φ, IsThetaFunO ψ S T Φ → (∀ h, IntegrableOn (fun g => thetaKO om g h Φ * φ g) fd ν) → ∃ Φ', IsThetaFunO ψ S T Φ' ∧ (∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → om (z, 1) Φ' = (χ z)⁻¹ • Φ') ∧ ∀ h, ∫ g in fd, thetaKO om g h Φ * φ g ∂ν = ∫ g in fd, thetaKO om g h Φ' * φ g ∂ν := by
  intro D ψ S T χS χT om hom hsig hdef ν fd hν hfd χ φ hcen hφ Φ hΦ hint
  by_cases hz : φ = 0
  · subst hz
    exact ⟨0, GlobalTheory.WeilVacMove.isTheta_zero, fun z _ _ => by simp, fun h => by simp⟩
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D S
  obtain ⟨j1, -, -, -, -, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D T
  let Z : Subgroup (GA D S) := GinfC S ⊓ Subgroup.center (GA D S)
  have hcl : IsClosed (Subgroup.center (GA D S) : Set (GA D S)) := by
    have : (Subgroup.center (GA D S) : Set (GA D S)) = ⋂ g, {a | g * a = a * g} := by
      ext a
      simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_iInter fun g => isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  haveI : CompactSpace Z :=
    isCompact_iff_compactSpace.mp ((Formalism.IndefR.Eqv.isCompact_GinfC hsig hdef).inter_right hcl)
  let m : Measure Z := GlobalTheory.haarProb Z
  obtain ⟨h₀, hh₀⟩ := Function.ne_iff.1 hz
  have hh : φ h₀ ≠ 0 := hh₀
  have hmul : ∀ a b : Z, χ (a * b : Z) = χ a * χ b := by
    intro a b
    apply mul_right_cancel₀ hh
    rw [← hcen _ (a * b).2.1 (a * b).2.2, Subgroup.coe_mul, ← mul_assoc, hcen _ b.2.1 b.2.2, hcen _ a.2.1 a.2.2]
    ring
  have hone : χ 1 = 1 := by
    apply mul_right_cancel₀ hh
    rw [← hcen _ (one_mem _) (one_mem _), mul_one, one_mul]
  have hcont : Continuous fun a : Z => χ a := by
    have : (fun a : Z => χ a) = fun a : Z => φ (h₀ * a) / φ h₀ := by
      funext a
      rw [hcen _ a.2.1 a.2.2, mul_div_cancel_right₀ _ hh]
    rw [this]
    exact (hφ.2.comp (continuous_const.mul continuous_subtype_val)).div_const _
  have hj : ∀ a : Z, (a : GA D S) ∈ GinfC S := fun a => a.2.1
  refine ⟨avg1 om m Subtype.val (fun a => χ a) Φ, isThetaFunction_average_compactFamily_weilTranslates m hom continuous_subtype_val hj hcont hΦ,
    fun a ha1 ha2 => ?_, fun h => ?_⟩
  · let a' : Z := ⟨a, ha1, ha2⟩
    have hne : χ a ≠ 0 := by
      intro h0
      have := hmul a'⁻¹ a'
      rw [inv_mul_cancel, OneMemClass.coe_one, hone] at this
      change 1 = χ (a'⁻¹ : Z) * χ a at this
      rw [h0, mul_zero] at this
      exact one_ne_zero this
    funext u
    rw [weilOperator_average_eq_average_translated m hom continuous_subtype_val hj hcont hΦ]
    simp only [Pi.smul_apply, smul_eq_mul, avg1]
    rw [← integral_mul_left_eq_self (μ := m) (fun b : Z => χ b * om ((b : GA D S), 1) Φ u) a', ← integral_const_mul]
    congr 1
    funext b
    rw [hmul a' b]
    change _ = (χ a)⁻¹ * (χ a * χ b * om ((a * b : GA D S), 1) Φ u)
    rw [Prod.mk_mul_mk, mul_one]
    field_simp
  · haveI : Countable (GQ S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig S.gram
    haveI : ν.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds S ν hν
    have hF_inv : ∀ γ ∈ GQ S, ∀ g, thetaKO om (γ * g) h Φ * φ (γ * g) = thetaKO om g h Φ * φ g := by
      intro γ hγ g
      have : om (γ * g, h) Φ 0 = om (g, h) Φ 0 := by
        rw [show ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) by rw [Prod.mk_mul_mk, one_mul], map_mul,
          Module.End.mul_apply, hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ hΦ)]
      simp only [thetaKO, this, hφ.1 γ hγ g]
    have hF_cont : Continuous fun g => thetaKO om g h Φ * φ g :=
      ((hom.om_cont Φ hΦ 0).comp (continuous_id.prodMk continuous_const)).mul hφ.2
    have key : ∀ g, thetaKO om g h (avg1 om m Subtype.val (fun a => χ a) Φ) * φ g =
        ∫ k : Z, thetaKO om (g * k) h Φ * φ (g * k) ∂m := by
      intro g
      unfold thetaKO
      rw [weilOperator_average_eq_average_translated m hom continuous_subtype_val hj hcont hΦ, ← integral_mul_const]
      congr 1
      funext k
      rw [Prod.mk_mul_mk, mul_one, hcen _ k.2.1 k.2.2]
      ring
    simp_rw [key]
    exact (GlobalTheory.Chain.IoLift.AvgLift.setIntegral_average (GQ S) ν hfd m continuous_subtype_val
      (Φ := fun g => thetaKO om g h Φ * φ g) hF_inv hF_cont (hint h)).symm

end GlobalTheory.CenAvgOne
