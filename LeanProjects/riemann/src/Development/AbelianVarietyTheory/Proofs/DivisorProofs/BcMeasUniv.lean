import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalInnerProductLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSurjectiveLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedFirstIsometricDualO1Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedSecondIsometricO1Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixGreenValueStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.ProjSpace GlobalTheory.HermFrame GlobalTheory.ArInt

namespace GlobalTheory.TautFlag

theorem selfInter (HC : GlobalTheory.Published.ArCalc) : haveI := ProjSpace.isRegSurf_line.isIntegral;
    (ProjSpace.hermitianTwistingSheaf ℤ 1).IsSelfInter (1 / 2) ∧ (ProjSpace.hermitianTwistingSheaf ℤ 1).dual.IsSelfInter (1 / 2) := by
  have := ProjSpace.isRegSurf_line.isIntegral
  have hP := ProjSpace.isArithVar_int 1
  obtain ⟨Ψ, hΨ⟩ := ((HC.arExists ℤ _ _ 1 hP).2 Unit fun _ => hermitianTwistingSheaf ℤ 1).1
  have h₁ := ((HC.arIso ℤ _ _ 1 hP).2 Unit _ Ψ hΨ).1 ()
  have hval : Ψ (MvPolynomial.X () ^ (1 + 1)) = 1 / 2 := FlagZ.Plane.selfInter_line (n := 1) rfl h₁
  have hΦ := ((HC.arIso ℤ _ _ 1 hP).2 Unit _ Ψ hΨ).2.2 Unit (fun _ => (hermitianTwistingSheaf ℤ 1).dual) (fun _ _ => -1)
    fun _ => HermLB.icls_eq_iff.1 (by
      rw [icls_comb, HermLB.icls_dual, Fintype.sum_unique]
      exact neg_one_zsmul _)
  have h₂ := ((HC.arIso ℤ _ _ 1 hP).2 Unit _ _ hΦ).1 ()
  refine ⟨hval ▸ h₁, ?_⟩
  convert h₂ using 1
  rw [← hval]
  simp [lin]

theorem exists_chart (σ : ℤ →+* ℂ) (j : Fin 2) : ∃ c : AlgChart (PSpace.str ℤ 1) σ 1,
    c.e.source = ptsIn _ σ (chart ℤ 1 j) ∧ c.e.target = Set.univ ∧
      ∀ y ∈ c.e.source, c.e y 0 = ev _ σ (chart ℤ 1 j) (ratio ℤ 1 j (j.succAbove 0)) y := by
  let e : MvPolynomial (Fin 1) ℤ ≃ₐ[ℤ] Γ(PSpace ℤ 1, chart ℤ 1 j) :=
    (MvPolynomial.renameEquiv ℤ (finSuccAboveEquiv j)).trans (chartAlgEquiv ℤ 1 j)
  have he : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (PSpace.str ℤ 1) (chart ℤ 1 j))
      (fun a => ratio ℤ 1 j (j.succAbove a)) = (e : MvPolynomial (Fin 1) ℤ →+* _) :=
    MvPolynomial.ringHom_ext (fun a => (MvPolynomial.eval₂Hom_C _ _ a).trans (e.commutes a).symm)
      fun b => (MvPolynomial.eval₂Hom_X' _ _ b).trans
        ((congrArg (chartAlgEquiv ℤ 1 j) (MvPolynomial.rename_X _ b)).trans
          (chartAlgEquiv_X ℤ 1 j (finSuccAboveEquiv j b))).symm
  obtain ⟨c, hs, ht, hx⟩ := FlagZ.Plane.exists_chart_of_bijective ℤ _ (PSpace.str ℤ 1) σ 1 _
    (isAffineOpen_chart ℤ 1 j) (fun a => ratio ℤ 1 j (j.succAbove a)) (by rw [he]; exact e.bijective)
  exact ⟨c, hs, ht, fun y hy => hx y hy 0⟩

theorem bcMeas_univ (σ : ℤ →+* ℂ) : ((stdH.h.stepMet flag 1).met σ).bcMeas (r := 1) (s := 1)
    (VMetric.stepSeq_shortExact flag 1) (flag.isVB (Fin.castSucc 1)) (flag.isVB_gr 1) Set.univ = 1 := by
  have := CxPts.secondCountableTopology_of_isProjOver σ (isProjOver_pspace_str ℤ 1)
  have H : ((stdH.h.stepMet flag 1).met σ).IsCInf := (stdH.cInf.restrict _ _) σ
  obtain ⟨c, hs, ht, hx⟩ := exists_chart σ 0
  obtain ⟨c', hs', -, hx'⟩ := exists_chart σ 1
  have hm : MeasurableSet c.e.source := c.e.open_source.measurableSet
  have hc (y : CxPts (PSpace.str ℤ 1) σ) (hy : y ∈ c.e.sourceᶜ) : y ∈ c'.e.source := by
    obtain ⟨j, hj⟩ := exists_mem_chart ℤ 1 (y.1 (IsLocalRing.closedPoint ℂ))
    rw [hs']
    rw [hs] at hy
    fin_cases j
    · exact absurd (mem_ptsIn.2 hj) hy
    · exact mem_ptsIn.2 hj
  have h₀ : ((stdH.h.stepMet flag 1).met σ).bcMeas (r := 1) (s := 1) (VMetric.stepSeq_shortExact flag 1)
      (flag.isVB (Fin.castSucc 1)) (flag.isVB_gr 1) c.e.sourceᶜ = 0 := by
    refine (Met.bcMeas_apply (r := 1) (s := 1) _ _ _ c' H hm.compl hc).trans
      (setLIntegral_measure_zero _ _ (measure_mono_null (t := {0}) ?_ (measure_singleton _)))
    rintro _ ⟨y, hy, rfl⟩
    have h₁ : c'.e y 0 = 0 := by
      rw [hx' y (hc y hy)]
      by_contra h
      have h₂ := (mem_ptsIn_basicOpen (hs' ▸ hc y hy) _).2 h
      rw [ratio, basicOpen_ratioOn] at h₂
      exact hy (hs ▸ (mem_ptsIn_inf.1 h₂).2)
    ext i
    rw [Subsingleton.elim i 0, h₁]
    rfl
  have hmem (v) : c.e.symm v ∈ c.e.source := c.e.map_target (ht ▸ trivial)
  have hr (v) : c.e (c.e.symm v) = v := c.e.right_inv (ht ▸ trivial)
  have hz (v) : ev _ σ (chart ℤ 1 0) (ratio ℤ 1 0 1) (c.e.symm v) = v 0 :=
    (hx _ (hmem v)).symm.trans (by rw [hr])
  have h1 (v) : ev _ σ (chart ℤ 1 0) (ratio ℤ 1 0 0) (c.e.symm v) = 1 := by
    rw [ev_eq (hs ▸ hmem v), ratio, ratioOn_self, map_one]
  have hG : (fun v => ((stdH.h.stepMet flag 1).met σ).gram (adapt₁ 0).frame (c.e.symm v)) =
      fun w : ReciprocityTheory.L2DbarEstimates.V 1 => (Matrix.fromBlocks (Matrix.of fun _ _ => 1 + w 0 * starRingEnd ℂ (w 0))
        (Matrix.of fun _ _ => w 0) (Matrix.of fun _ _ => starRingEnd ℂ (w 0)) 1 :
          Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) := funext fun v => by
    have e₁ : nsqV 0 (c.e.symm v) = 1 + v 0 * starRingEnd ℂ (v 0) := by
      rw [nsqV, h1, hz, map_one, mul_one]
    have e₂ : ipVT 0 (c.e.symm v) = v 0 := hz v
    rw [gram_adapt₁ 0 (hs ▸ hmem v), e₁, e₂]
  have hd (v) : ((stdH.h.stepMet flag 1).met σ).bcDens (r := 1) (s := 1) (VMetric.stepSeq_shortExact flag 1)
      (flag.isVB (Fin.castSucc 1)) (flag.isVB_gr 1) c (c.e.symm v) =
        1 / Real.pi * (ArithHeightModel.u v ^ 2)⁻¹ := by
    refine (Met.bcDens_eq (r := 1) (s := 1) _ _ _ (adapt₁ 0) c H (hmem v) (hs ▸ hmem v)).trans ?_
    refine Eq.trans ?_ (GlobalTheory.T.hermitian_matrix_green_value v)
    exact congrArg₂ (fun K w => 2 * diagVal (extTrace K w) (EuclideanSpace.single 0 1)) hG (hr v)
  have hn (v : ReciprocityTheory.L2DbarEstimates.V 1) : 0 ≤ 1 / Real.pi * (ArithHeightModel.u v ^ 2)⁻¹ := by
    have := Real.pi_pos; positivity
  rw [← measure_add_measure_compl hm, h₀, add_zero]
  refine (Met.bcMeas_apply (r := 1) (s := 1) _ _ _ c H hm subset_rfl).trans ?_
  rw [c.e.image_source_eq_target, ht, Measure.restrict_univ]
  refine (lintegral_congr fun v => congrArg ENNReal.ofReal (hd v)).trans ?_
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.of_integral_ne_zero
    (ArithHeightModel.integral_dens.trans_ne one_ne_zero)) (.of_forall hn), ArithHeightModel.integral_dens,
    ENNReal.ofReal_one]

theorem flagBc_flag : stdH.h.FlagBcFinite flag ∧ stdH.h.flagBc flag = 1 := by
  have e (σ) : ((stdH.h.stepMet flag 0).met σ).bcMeas (VMetric.stepSeq_shortExact flag 0)
      (flag.isVB (Fin.castSucc 0)) (flag.isVB_gr 0) = 0 := Met.bcMeas_rank_zero _ _ _
  have e' (σ) : ((stdH.h.stepMet flag 1).met σ).bcMeas (VMetric.stepSeq_shortExact flag 1)
      (flag.isVB (Fin.castSucc 1)) (flag.isVB_gr 1) Set.univ = 1 := bcMeas_univ σ
  refine ⟨Fin.forall_fin_two.2 ⟨fun σ => ?_, fun σ => ?_⟩, ?_⟩
  · exact (congrArg (fun μ : Measure _ => μ Set.univ) (e σ)).trans_ne ENNReal.zero_ne_top
  · exact (e' σ).trans_ne ENNReal.one_ne_top
  · rw [VMetric.flagBc, Fin.sum_univ_two]
    refine (congrArg₂ (· + ·) (finsum_eq_zero_of_forall_eq_zero fun σ => ?_)
      ((finsum_eq_single _ (Int.castRingHom ℂ) fun σ h => absurd (RingHom.ext_int _ _) h).trans ?_)).trans
        (zero_add 1)
    · exact congrArg (fun μ : Measure _ => (μ Set.univ).toReal) (e σ)
    · exact congrArg ENNReal.toReal (e' _)

theorem exists_flag : GlobalTheory.Published.ArCalc → haveI := ProjSpace.isRegSurf_line.isIntegral;
    ∃ fl : Vert.Flag (HermVB.std (PSpace.str ℤ 1) 2).E 2,
      (VMetric.grLB fl 0 (HermVB.std (PSpace.str ℤ 1) 2).cInf).Isometric (ProjSpace.hermitianTwistingSheaf ℤ 1).dual ∧
        (HermVB.std (PSpace.str ℤ 1) 2).h.flagBc fl = 1 ∧
          VMetric.IsFlagCh2 (HermVB.std (PSpace.str ℤ 1) 2).cInf fl 0 := fun HC => by
  have := ProjSpace.isRegSurf_line.isIntegral
  obtain ⟨s₁, s₂⟩ := selfInter HC
  have hX := ProjSpace.isArithVar_int 1
  refine ⟨flag, GlobalTheory.T.graded_first_isometric_dual_O1, flagBc_flag.2, flagBc_flag.1, ![1 / 2, 1 / 2], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact GlobalTheory.T.graded_first_isometric_dual_O1.symm.isSelfInter hX s₂
    · exact GlobalTheory.T.graded_second_isometric_O1.symm.isSelfInter hX s₁
  · rw [flagBc_flag.2, Fin.sum_univ_two]
    norm_num

end GlobalTheory.TautFlag
