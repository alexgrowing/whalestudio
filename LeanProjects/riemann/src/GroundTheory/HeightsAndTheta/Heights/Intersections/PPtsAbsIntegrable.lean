import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsAbsIntegrable
import GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsAbsMeasurable
import GroundTheory.HeightsAndTheta.Heights.Intersections.RegLine
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRSlotAdd
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemiPosTwist
import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSheetHessPSD
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMixSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ComplexOrder

namespace PointsAbsIntegrable

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem cxHessian_tensor {D : ℕ} {X Y : HermLine ι} (hX : IsSmoothHerm X) (hY : IsSmoothHerm Y)
    {γ : (Fin D → ℂ) → (Σ k, ι k) → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0) :
    cxHessian (fun y' => Real.log ((X.tensor Y).h (γ y'))) y =
      cxHessian (fun y' => Real.log (X.h (γ y'))) y + cxHessian (fun y' => Real.log (Y.h (γ y'))) y := by
  have hev := hγ.eventually_nhds
  have ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (X.h (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact contDiffAt_log_metric hX (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hc : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (Y.h (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact contDiffAt_log_metric hY (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hψ : (fun y' => Real.log ((X.tensor Y).h (γ y'))) =ᶠ[𝓝 y]
      fun y' => 1 * Real.log (X.h (γ y')) + 1 * Real.log (Y.h (γ y')) := by
    filter_upwards [hγ] with y' hy'
    rw [one_mul, one_mul]
    exact Real.log_mul (X.pos _ hy'.2).ne' (Y.pos _ hy'.2).ne'
  have hH := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaamix_cxHessian_comb 1 1 ha hc hψ
  simpa only [Complex.ofReal_one, one_smul] using hH

theorem abs_maDensity_le {P : Ideal (MRing ι)} {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {L T : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) (hT : ∀ j, IsSmoothHerm (T j))
    (hTp : ∀ j, IsSemiPosHerm (T j)) (hLTp : ∀ j, IsSemiPosHerm ((L j).tensor (T j)))
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (hS : IsSheet P Ψ y w γ) :
    |maDensity (fun j y' => pot L j (γ y')) y| ≤
      3 ^ e * maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y := by
  have hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0 := by
    filter_upwards [hS.2] with y' hy'
    exact ⟨hy'.1, hy'.2.1.1⟩
  have hLT : ∀ j, IsSmoothHerm ((L j).tensor (T j)) := fun j => isSmoothHerm_tensor (hL j) (hT j)
  set A : Fin e → Matrix (Fin e) (Fin e) ℂ := fun j => cxHessian (fun y' => pot L j (γ y')) y with hAdef
  set B : Fin e → Matrix (Fin e) (Fin e) ℂ :=
    fun j => cxHessian (fun y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y with hBdef
  have hHT : ∀ j, (cxHessian (fun y' => Real.log ((T j).h (γ y'))) y).PosSemidef := fun j =>
    SheetHessPSD.proof K ι P e Ψ (T j) y w γ (hT j) (hTp j) hS
  have hHLT : ∀ j, (cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y).PosSemidef := fun j =>
    SheetHessPSD.proof K ι P e Ψ _ y w γ (hLT j) (hLTp j) hS
  have hB : ∀ j, B j = cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y +
      cxHessian (fun y' => Real.log ((T j).h (γ y'))) y := fun j =>
    cxHessian_tensor (hLT j) (hT j) hγ
  have hA : ∀ j, cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y =
      A j + cxHessian (fun y' => Real.log ((T j).h (γ y'))) y := fun j =>
    cxHessian_tensor (hL j) (hT j) hγ
  have hle : ∀ j, (B j - A j).PosSemidef := fun j => by
    have e1 : B j - A j = cxHessian (fun y' => Real.log ((T j).h (γ y'))) y +
        cxHessian (fun y' => Real.log ((T j).h (γ y'))) y := by
      rw [hB j, hA j]; abel
    rw [e1]
    exact (hHT j).add (hHT j)
  have hge : ∀ j, (A j + B j).PosSemidef := fun j => by
    have e1 : A j + B j = cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y +
        cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y := by
      rw [hB j, hA j]; abel
    rw [e1]
    exact (hHLT j).add (hHLT j)
  have hn : ‖mixedDisc A‖ ≤ 3 ^ e * (mixedDisc B).re :=
    ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le A B hle hge
  have hc : 0 ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e := by positivity
  unfold maDensity
  rw [abs_mul, abs_of_nonneg hc]
  calc (e.factorial : ℝ) * (2 / Real.pi) ^ e * |(mixedDisc A).re|
      ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e * (3 ^ e * (mixedDisc B).re) :=
        mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hn) hc
    _ = 3 ^ e * ((e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc B).re) := by ring

end PointsAbsIntegrable

open PointsAbsIntegrable in

theorem PtsAbsIntegrable.proof (hInt : PtsIntegrableStatement) (hMeas : PtsAbsMeasurable.Statement) :
    PtsAbsIntegrable.Statement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  classical
  have hTw := SemiPosTwist.proof TorusInvLevi.proof
  choose T hTs hTp hLTp using fun j => hTw K ι (L j) (hL j)
  have hN : ∀ j, IsSmoothHerm (((L j).tensor (T j)).tensor (T j)) := fun j =>
    isSmoothHerm_tensor (isSmoothHerm_tensor (hL j) (hTs j)) (hTs j)
  obtain ⟨a, ha, hsa, hsP⟩ := hs
  have hs : IsSectionOn P A s := ⟨a, ha, hsa, hsP⟩
  set D := regLine A s ⟨a, ha, hsa⟩ 1 with hDdef
  have hD : IsSmoothHerm D := isSmoothHerm_regLine hA one_pos
  have hD1 : IsSectionOn P D 1 := by
    refine ⟨0, fun k => by simp [hDdef, regLine_a], fun m hm k => ?_,
      fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)⟩
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  have h1 := hInt K ι P e Ψ _ A s hP hΨ hN hA hs
  have h2 := hInt K ι P e Ψ _ D 1 hP hΨ hN hD hD1

  have key : ∀ y w, |sheetDensity P Ψ (pot L) (logNorm A s) y w| ≤
      3 ^ e * (-2 * sheetDensity P Ψ (pot fun j => ((L j).tensor (T j)).tensor (T j)) (logNorm D 1) y w -
        sheetDensity P Ψ (pot fun j => ((L j).tensor (T j)).tensor (T j)) (logNorm A s) y w) := by
    intro y w
    unfold sheetDensity
    by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
    · simp only [dif_pos hγ]
      set γ := hγ.choose
      have hS : IsSheet P Ψ y w γ := hγ.choose_spec
      have hmem : γ y ∈ mcPts P := hS.2.self_of_nhds.2.1
      have hm := abs_maDensity_le hL hTs hTp hLTp hS
      set r := Real.log (D.h (γ y)) with hr
      have hr0 : 0 ≤ r := by
        rw [hr, hDdef, log_regLine_h]
        exact div_nonneg (Real.log_nonneg (by nlinarith [sq_nonneg (secNorm A s (γ y))])) (by norm_num)
      have hgr : logNorm A s (γ y) ≤ r := by
        by_cases h0 : eval (γ y) (map (Int.castRingHom ℂ) s) = 0
        · have : logNorm A s (γ y) = 0 := by simp [logNorm, h0]
          rw [this]
          exact hr0
        · exact logNorm_le_log_regLine_h zero_le_one hmem.1 h0
      have hD1r : logNorm D 1 (γ y) = -r := by
        simp [logNorm, hr, Real.log_inv]
      rw [hD1r]
      have hg : |logNorm A s (γ y)| ≤ 2 * r - logNorm A s (γ y) := by
        rw [abs_le]
        constructor <;> linarith
      rw [abs_mul]
      calc |logNorm A s (γ y)| * |maDensity (fun j y' => pot L j (γ y')) y|
          ≤ (2 * r - logNorm A s (γ y)) *
              (3 ^ e * maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y) :=
            mul_le_mul hg hm (abs_nonneg _) (by linarith [abs_nonneg (logNorm A s (γ y))])
        _ = _ := by ring
    · simp only [dif_neg hγ]
      simp
  refine Integrable.mono' (((h2.const_mul (-2)).sub h1).const_mul (3 ^ e))
    (hMeas K ι P e Ψ L A s hP hΨ hL hA hs) (Eventually.of_forall fun y => ?_)
  have hfin := fibreFinite K ι P e Ψ hP hΨ y
  simp only [Pi.sub_apply]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _), Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun w _ => key y w

end GroundTheory.Heights₂.Heights.Inter
