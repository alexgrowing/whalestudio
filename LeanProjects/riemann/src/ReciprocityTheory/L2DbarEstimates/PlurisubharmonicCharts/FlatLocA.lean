import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

open Complex ComplexConjugate Filter Topology
open scoped ContDiff

namespace ReciprocityTheory.L2DbarEstimates.Y

noncomputable section

variable {n : ℕ}

theorem I_pow_three_eq_neg_I : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring

theorem flA_expand (w : V n) : w = ∑ j, w j • bas n j := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr w]
  simp [bas]

theorem flA_apply_sum (D : V n →L[ℂ] V n) (ξ : Fin n → ℂ) (a : Fin n) :
    D (WithLp.toLp 2 ξ) a = ∑ j, ξ j * D (bas n j) a := by
  conv_lhs => rw [flA_expand (WithLp.toLp 2 ξ)]
  simp [map_sum, map_smul]

theorem flA_decomp (D : V n →L[ℝ] ℂ) (w : V n) :
    D w = ∑ b, (w b * ((D (bas n b) - I * D (I • bas n b)) / 2) +
      conj (w b) * ((D (bas n b) + I * D (I • bas n b)) / 2)) := by
  conv_lhs => rw [flA_expand w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hcb : w b • bas n b = (w b).re • bas n b + (w b).im • (I • bas n b) := by
    conv_lhs => rw [← Complex.re_add_im (w b)]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  rw [hcb, map_add, map_smul, map_smul]
  conv_rhs => rw [← Complex.re_add_im (w b)]
  simp only [Complex.real_smul, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring_nf; simp only [I_sq]; ring_nf

theorem flA_fderiv_comp {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : DifferentiableAt ℝ U (G y)) (hG : DifferentiableAt ℂ G y) (v : V n) :
    fderiv ℝ (U ∘ G) y v = fderiv ℝ U (G y) (fderiv ℂ G y v) := by
  rw [(hU.hasFDerivAt.comp y (hG.hasFDerivAt.restrictScalars ℝ)).fderiv]; rfl

theorem flA_wdb_comp {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : DifferentiableAt ℝ U (G y)) (hG : DifferentiableAt ℂ G y) (k : Fin n) :
    wdb n k (U ∘ G) y = ∑ b, wdb n b U (G y) * conj (fderiv ℂ G y (bas n k) b) := by
  simp only [wdb]
  rw [flA_fderiv_comp hU hG, flA_fderiv_comp hU hG, map_smul,
    flA_decomp (fderiv ℝ U (G y)) (fderiv ℂ G y (bas n k)),
    flA_decomp (fderiv ℝ U (G y)) (I • fderiv ℂ G y (bas n k))]
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring_nf; simp only [I_sq, I_pow_three_eq_neg_I]; ring_nf

theorem flA_wd_comp {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : DifferentiableAt ℝ U (G y)) (hG : DifferentiableAt ℂ G y) (k : Fin n) :
    wd n k (U ∘ G) y = ∑ b, wd n b U (G y) * fderiv ℂ G y (bas n k) b := by
  simp only [wd]
  rw [flA_fderiv_comp hU hG, flA_fderiv_comp hU hG, map_smul,
    flA_decomp (fderiv ℝ U (G y)) (fderiv ℂ G y (bas n k)),
    flA_decomp (fderiv ℝ U (G y)) (I • fderiv ℂ G y (bas n k))]
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring_nf; simp only [I_sq, I_pow_three_eq_neg_I]; ring_nf

theorem sum_four_comm_bis (T : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, ∑ j, ∑ k, T a b j k = ∑ j, ∑ k, ∑ b, ∑ a, T a b j k := by
  calc ∑ a, ∑ b, ∑ j, ∑ k, T a b j k = ∑ a, ∑ j, ∑ k, ∑ b, T a b j k := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => ?_; rw [Finset.sum_comm]
    _ = ∑ j, ∑ k, ∑ b, ∑ a, T a b j k := by
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _ => ?_; rw [Finset.sum_comm]

theorem flA_diff_comp_apply {G : V n → V n} {y : V n} (hG : ContDiffAt ℂ 2 G y) (k b : Fin n) :
    DifferentiableAt ℂ (fun v => fderiv ℂ G v (bas n k) b) y := by
  have hD1 : DifferentiableAt ℂ (fderiv ℂ G) y :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  exact (EuclideanSpace.proj b : V n →L[ℂ] ℂ).differentiableAt.comp y
    (hD1.clm_apply (differentiableAt_const _))

theorem flA_leviV_comp {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : ContDiffAt ℝ 2 U (G y)) (hG : ContDiffAt ℂ 2 G y) (ξ : Fin n → ℂ) :
    leviV n (U ∘ G) y ξ = leviV n U (G y) (fun b => fderiv ℂ G y (WithLp.toLp 2 ξ) b) := by
  have hGy : DifferentiableAt ℂ G y := hG.differentiableAt (by simp)
  have hGd : ∀ᶠ v in 𝓝 y, DifferentiableAt ℂ G v :=
    (hG.eventually (by simp)).mono fun v hv => hv.differentiableAt (by simp)
  have hUd : ∀ᶠ v in 𝓝 y, DifferentiableAt ℝ U (G v) :=
    hG.continuousAt.tendsto.eventually (eventually_differentiableAt_of_contDiffAt hU)
  have hev : ∀ k, wdb n k (U ∘ G) =ᶠ[𝓝 y]
      fun v => ∑ b, wdb n b U (G v) * conj (fderiv ℂ G v (bas n k) b) := by
    intro k; filter_upwards [hGd, hUd] with v h1 h2; exact flA_wdb_comp h2 h1 k
  have hA : ∀ b, DifferentiableAt ℝ (fun v => wdb n b U (G v)) y := fun b =>
    (differentiableAt_wdb hU).comp y (hGy.restrictScalars ℝ)
  have hB := flA_diff_comp_apply hG
  have hwd : ∀ j k, wd n j (wdb n k (U ∘ G)) y = ∑ b, (∑ a, wd n a (wdb n b U) (G y) *
      fderiv ℂ G y (bas n j) a) * conj (fderiv ℂ G y (bas n k) b) := by
    intro j k
    have hc : ∀ b, DifferentiableAt ℝ (fun v => conj (fderiv ℂ G v (bas n k) b)) y := fun b =>
      differentiableAt_conj ((hB k b).restrictScalars ℝ)
    rw [wd_congr (hev k), wd_sum Finset.univ
      (f := fun b v => wdb n b U (G v) * conj (fderiv ℂ G v (bas n k) b))
      (fun b _ => (hA b).mul (hc b))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [wd_mul (hA b) (hc b), wd_conj ((hB k b).restrictScalars ℝ),
      wdb_of_differentiableAt (hB k b)]
    rw [show (fun v => wdb n b U (G v)) = wdb n b U ∘ G from rfl,
      flA_wd_comp (differentiableAt_wdb hU) hGy j]
    simp
  simp only [leviV]
  simp_rw [hwd, flA_apply_sum]
  simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [sum_four_comm_bis, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem flA_leviV_log_normSq {h : V n → ℂ} {y : V n}
    (hh : ∀ᶠ v in 𝓝 y, DifferentiableAt ℂ h v) (hne : h y ≠ 0) (ξ : Fin n → ℂ) :
    leviV n (fun v => ((Real.log (‖h v‖ ^ 2) : ℝ) : ℂ)) y ξ = 0 := by
  set Lf : V n → ℂ := fun v => Complex.log (h v / h y) with hLf
  have hcont : ContinuousAt (fun v => h v / h y) y :=
    (hh.self_of_nhds.continuousAt).div_const _
  have hslit : ∀ᶠ v in 𝓝 y, h v / h y ∈ Complex.slitPlane := by
    apply hcont.eventually_mem
    rw [div_self hne]
    exact Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane
  have hLd : ∀ᶠ v in 𝓝 y, DifferentiableAt ℂ Lf v := by
    filter_upwards [hh, hslit] with v h1 h2
    have h3 : DifferentiableAt ℂ (fun v => h v / h y) v := by
      simpa [div_eq_mul_inv] using h1.mul_const (h y)⁻¹
    exact h3.clog h2
  obtain ⟨t, ht, hto, hyt⟩ := eventually_nhds_iff.mp hLd
  have hLc : ContDiffOn ℂ ∞ Lf t := contDiffOn_of_differentiableOn n Lf t hto
    (fun v hv => (ht v hv).differentiableWithinAt)
  have hL2 : ∀ v ∈ t, ContDiffAt ℂ 2 Lf v := fun v hv =>
    ((hLc v hv).contDiffAt (hto.mem_nhds hv)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hne' : ∀ᶠ v in 𝓝 y, h v ≠ 0 := hh.self_of_nhds.continuousAt.eventually_ne hne
  have hF : (fun v => ((Real.log (‖h v‖ ^ 2) : ℝ) : ℂ)) =ᶠ[𝓝 y]
      fun v => ((Real.log (‖h y‖ ^ 2) : ℝ) : ℂ) + Lf v + conj (Lf v) := by
    filter_upwards [hne'] with v hv
    have h1 : Lf v + conj (Lf v) = ((2 * (Lf v).re : ℝ) : ℂ) := by
      rw [Complex.add_conj]
    rw [add_assoc, h1, Complex.log_re, norm_div]
    rw [Real.log_div (norm_ne_zero_iff.mpr hv) (norm_ne_zero_iff.mpr hne), Real.log_pow,
      Real.log_pow]
    push_cast; try ring
  rw [leviV_congr hF]
  have hwdb : ∀ k, wdb n k (fun v => ((Real.log (‖h y‖ ^ 2) : ℝ) : ℂ) + Lf v + conj (Lf v))
      =ᶠ[𝓝 y] fun v => conj (wd n k Lf v) := by
    intro k
    filter_upwards [hto.mem_nhds hyt] with v hv
    have hd : DifferentiableAt ℂ Lf v := ht v hv
    rw [wdb_add (f := fun v => ((Real.log (‖h y‖ ^ 2) : ℝ) : ℂ) + Lf v) (g := fun v => conj (Lf v))
        ((differentiableAt_const _).add (hd.restrictScalars ℝ))
        (differentiableAt_conj (hd.restrictScalars ℝ)),
      wdb_add (f := fun _ => ((Real.log (‖h y‖ ^ 2) : ℝ) : ℂ)) (g := Lf)
        (differentiableAt_const _) (hd.restrictScalars ℝ),
      wdb_conj (hd.restrictScalars ℝ), wdb_of_differentiableAt hd,
      wdb_of_differentiableAt (differentiableAt_const _)]
    ring
  have hz : ∀ j k, wd n j (wdb n k (fun v => ((Real.log (‖h y‖ ^ 2) : ℝ) : ℂ) + Lf v +
      conj (Lf v))) y = 0 := by
    intro j k
    have hwk : wd n k Lf =ᶠ[𝓝 y] fun v => fderiv ℂ Lf v (bas n k) := by
      filter_upwards [hto.mem_nhds hyt] with v hv
      exact wd_of_differentiableAt (ht v hv)
    have hdk : DifferentiableAt ℂ (fun v => fderiv ℂ Lf v (bas n k)) y :=
      (((hL2 y hyt).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
        (differentiableAt_const _)
    rw [wd_congr (hwdb k), wd_conj (differentiableAt_wd (hL2 y hyt |>.restrict_scalars ℝ)),
      wdb_congr hwk, wdb_of_differentiableAt hdk]
    simp
  simp only [leviV, hz, zero_mul, Finset.sum_const_zero]

theorem flA_leviV_add {F G : V n → ℝ} {y : V n} (hF : ContDiffAt ℝ 2 F y)
    (hG : ContDiffAt ℝ 2 G y) (ξ : Fin n → ℂ) :
    leviV n (fun v => ((F v + G v : ℝ) : ℂ)) y ξ =
      leviV n (fun v => (F v : ℂ)) y ξ + leviV n (fun v => (G v : ℂ)) y ξ := by
  have hFc : ContDiffAt ℝ 2 (fun v => (F v : ℂ)) y := ofRealCLM.contDiff.contDiffAt.comp y hF
  have hGc : ContDiffAt ℝ 2 (fun v => (G v : ℂ)) y := ofRealCLM.contDiff.contDiffAt.comp y hG
  have hfun : (fun v => ((F v + G v : ℝ) : ℂ)) = fun v => (F v : ℂ) + (G v : ℂ) := by
    funext v; push_cast; rfl
  have hev : ∀ k, wdb n k (fun v => (F v : ℂ) + (G v : ℂ)) =ᶠ[𝓝 y]
      fun v => wdb n k (fun v => (F v : ℂ)) v + wdb n k (fun v => (G v : ℂ)) v := by
    intro k
    filter_upwards [eventually_differentiableAt_of_contDiffAt hFc,
      eventually_differentiableAt_of_contDiffAt hGc] with v h1 h2
    exact wdb_add h1 h2
  rw [hfun]
  simp only [leviV]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [wd_congr (hev k), wd_add (differentiableAt_wdb hFc) (differentiableAt_wdb hGc)]
  ring

end

end ReciprocityTheory.L2DbarEstimates.Y
