import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DifferentiableChart
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChartSubFormEntryLe
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeviWeightChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem nmat_hasDerivAt (X : Data E r) {f : ℂ → V (nd X)} {f' : V (nd X)} {t : ℂ}
    (hf : HasDerivAt f f' t) (τ : X.Ψ) (a c : Fin r) :
    HasDerivAt (fun s => nmat X (f s) τ a c) (nmat X f' τ a c - if a = c then 1 else 0) t := by
  unfold nmat
  by_cases h : c < a
  · simp only [h, dif_pos, h.ne', if_false, sub_zero]
    exact
      ((PiLp.proj 2 (fun _ : Fin (nd X) => ℂ) ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, c), h⟩⟩)).hasFDerivAt).comp_hasDerivAt t hf
  · simp only [h, dif_neg, not_false_eq_true, sub_self]
    exact hasDerivAt_const _ _

theorem nmat_zero_apply (X : Data E r) (τ : X.Ψ) (a c : Fin r) :
    nmat X 0 τ a c = if a = c then 1 else 0 := by
  have := congrFun (congrFun (IW.nmat_zero X τ) a) c
  simpa [mat, Matrix.one_apply] using this

theorem levi_transport_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 x1 b : Frame X.Ψ r) (z : V (nd X)), IsOrth X x1 → z ∈ OmF X x0 → b ∈ Bor X.Ψ r → cpt X x0 z = rmul x1 b → ∀ ξ : Fin (nd X) → ℂ, ∃ ξ' : Fin (nd X) → ℂ, (∀ la : Wt X.Ψ r, leviM X (phla X la) x0 z ξ = leviM X (phla X la) x1 0 ξ') ∧ ∃ B : Frame X.Ψ r, (∀ τ (a c : Fin r), c < a → B τ a c = 0) ∧ ∀ τ, mat x0 τ * (mat (nmat X (WithLp.toLp 2 ξ)) τ - 1) = mat x1 τ * ((mat (nmat X (WithLp.toLp 2 ξ')) τ - 1) * mat b τ + mat B τ) := by
  intro E _ _ _ r X x0 x1 b z ho hz hb hxb ξ
  have hz1 : (0 : V (nd X)) ∈ OmF X x1 := IW.zero_mem_OmF X x1 ho
  have hxb' : cpt X x0 z = rmul (cpt X x1 0) b := by rw [IW.cpt_zero]; exact hxb
  obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, hbd, hsplit, hinv⟩ := lu_holds r X x1 ho
  have h0 := hinv 0 hz1 b hb
  rw [← hxb'] at h0
  have hcd : Differentiable ℂ (cpt X x0) := IW.cpt_diff X x0
  set U : Set (V (nd X)) := {w | cpt X x0 w ∈ X.dom ∧ Δ (cpt X x0 w) ≠ 0} with hUdef
  have hU : IsOpen U :=
    (ExF.isOpen_OmF X x0).inter (isOpen_compl_singleton.preimage (hΔ.comp hcd).continuous)
  have hzU : z ∈ U := ⟨hz, h0.1⟩
  set Φ : V (nd X) → V (nd X) := fun w => zOf (cpt X x0 w) with hΦdef
  set bf : V (nd X) → Frame X.Ψ r := fun w => bOf (cpt X x0 w) with hbfdef
  have hΦ : DifferentiableOn ℂ Φ U := hzd.comp hcd.differentiableOn fun w hw => hw
  have hbf : DifferentiableOn ℂ bf U := hbd.comp hcd.differentiableOn fun w hw => hw
  have hΦz : Φ z = 0 := h0.2.1
  have hbz : bf z = b := h0.2.2
  have hΦ2 : ContDiffOn ℂ 2 Φ U := by
    rw [contDiffOn_piLp]
    intro i
    exact (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ U hU
      ((differentiableOn_piLp 2).1 hΦ i)).of_le HE.two_le_inf
  set v : V (nd X) := WithLp.toLp 2 ξ with hv
  have hγ : HasDerivAt (fun t : ℂ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
  have hγU : ∀ᶠ t in 𝓝 (0 : ℂ), z + t • v ∈ U := by
    have h := (hγ.continuousAt)
    simp only [ContinuousAt, zero_smul, add_zero] at h
    exact h (hU.mem_nhds hzU)
  have hbfD : HasDerivAt (fun t : ℂ => bf (z + t • v)) (fderiv ℂ bf z v) 0 :=
    (hbf.differentiableAt (hU.mem_nhds hzU)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ (by simp)
  have hΦD : HasDerivAt (fun t : ℂ => Φ (z + t • v)) (fderiv ℂ Φ z v) 0 :=
    (hΦ.differentiableAt (hU.mem_nhds hzU)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ (by simp)
  have hbfE : ∀ τ a c, HasDerivAt (fun t : ℂ => bf (z + t • v) τ a c) (fderiv ℂ bf z v τ a c) 0 :=
    fun τ a c => hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_pi.1 hbfD τ) a) c
  refine ⟨fun k => (fderiv ℂ Φ z v).ofLp k, fun la => ?_, fderiv ℂ bf z v, ?_, ?_⟩
  · have hch : DifferentiableOn ℂ (fun w => bchar la (bf w)) U := by
      classical
      intro w hw
      unfold bchar
      refine DifferentiableAt.differentiableWithinAt ?_
      refine (HasFDerivAt.finsetProd (g' := fun τ => fderiv ℂ (fun w => ∏ i, bf w τ i i ^ la τ i) w)
        fun τ _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
      refine (HasFDerivAt.finsetProd (g' := fun i => fderiv ℂ (fun w => bf w τ i i ^ la τ i) w)
        fun i _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
      have hw' : DifferentiableAt ℂ bf w := hbf.differentiableAt (hU.mem_nhds hw)
      have hi : DifferentiableAt ℂ (fun w => bf w τ i i) w :=
        differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_pi.1 hw' τ) i) i
      have hzp : DifferentiableAt ℂ (fun t : ℂ => t ^ la τ i) (bf w τ i i) :=
        differentiableAt_zpow.2
          (Or.inl (GlobalTheory.LeviTransfer.borel_diag_ne_zero (hsplit _ hw.1 hw.2).2.1 τ i))
      exact DifferentiableAt.comp (g := fun t : ℂ => t ^ la τ i) w hzp hi
    have hchz : ContDiffAt ℂ 2 (fun w => bchar la (bf w)) z :=
      (HE.contDiffAt_of_punct hU hch hzU).of_le HE.two_le_inf
    have hne : bchar la (bf z) ≠ 0 := IW.bchar_ne_zero X (hsplit _ hz h0.1).2.1 _
    have hev : (fun w => ((phla X la (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
        fun w => ((phla X la (cpt X x1 (Φ w)) + Real.log (Complex.normSq (bchar la (bf w))) : ℝ) : ℂ) := by
      filter_upwards [hU.mem_nhds hzU] with w hw
      obtain ⟨h1, h2, h3⟩ := hsplit _ hw.1 hw.2
      rw [← GlobalTheory.LeviTransfer.metric_rmul normFactor_rightBorel_holds X la h1 h2, ← h3]
    have hg : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 w)) (Φ z) := by
      rw [hΦz]
      exact (IW.phla_cpt_cdAt X x1 hz1 la).of_le HE.two_le_inf
    have h1 : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 (Φ w))) z :=
      hg.comp z ((hΦ2.contDiffAt (hU.mem_nhds hzU)).restrict_scalars ℝ)
    have h2 : ContDiffAt ℝ 2 (fun w => Real.log (Complex.normSq (bchar la (bf w)))) z :=
      (HE.normSq_contDiffAt hchz).log (Complex.normSq_pos.2 hne).ne'
    have hgC : ContDiffAt ℝ 2 (fun w => ((phla X la (cpt X x1 w) : ℝ) : ℂ)) (Φ z) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp _ hg
    have hc := RGF.gc_leviV_comp _ _ _ Φ U hU z hzU hΦ2 hgC ξ
    rw [hΦz] at hc
    unfold leviM
    rw [leviV_congr hev, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 h2,
      HE.levi_logNormSq_zero_at _ z hchz hne ξ, add_zero]
    exact congrArg Complex.re hc
  · intro τ a c hca
    have hev : (fun t : ℂ => bf (z + t • v) τ a c) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [hγU] with t ht
      exact ((hsplit _ ht.1 ht.2).2.1 τ).2 a c hca
    exact (hbfE τ a c).unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hev)
  · intro τ
    ext a c
    have hL : HasDerivAt (fun t : ℂ => ∑ k, x0 τ a k * nmat X (z + t • v) τ k c)
        (∑ k, x0 τ a k * (nmat X v τ k c - if k = c then 1 else 0)) 0 :=
      HasDerivAt.fun_sum fun k _ => (nmat_hasDerivAt X hγ τ k c).const_mul _
    have hR : HasDerivAt (fun t : ℂ => ∑ k, (∑ l, x1 τ a l * nmat X (Φ (z + t • v)) τ l k) * bf (z + t • v) τ k c)
        (∑ k, ((∑ l, x1 τ a l * (nmat X (fderiv ℂ Φ z v) τ l k - if l = k then 1 else 0)) * bf (z + (0:ℂ) • v) τ k c
          + (∑ l, x1 τ a l * nmat X (Φ (z + (0:ℂ) • v)) τ l k) * fderiv ℂ bf z v τ k c)) 0 :=
      HasDerivAt.fun_sum fun k _ =>
        (HasDerivAt.fun_sum fun l _ => (nmat_hasDerivAt X hΦD τ l k).const_mul _).fun_mul (hbfE τ k c)
    have hev : (fun t : ℂ => ∑ k, x0 τ a k * nmat X (z + t • v) τ k c) =ᶠ[𝓝 0]
        fun t : ℂ => ∑ k, (∑ l, x1 τ a l * nmat X (Φ (z + t • v)) τ l k) * bf (z + t • v) τ k c := by
      filter_upwards [hγU] with t ht
      have e0 : cpt X x0 (z + t • v) = rmul (cpt X x1 (Φ (z + t • v))) (bf (z + t • v)) :=
        (hsplit _ ht.1 ht.2).2.2
      have e := congrFun (congrFun (congrFun e0 τ) a) c
      simp only [cpt, rmul, mat, Matrix.mul_apply, Matrix.of_apply] at e
      exact e
    have heq := hL.unique (hR.congr_of_eventuallyEq hev)
    simp only [zero_smul, add_zero, hΦz, hbz, nmat_zero_apply] at heq
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, mat, Matrix.of_apply,
      WithLp.toLp_ofLp]
    rw [heq]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]

end GlobalTheory.LeviWeightChart
