import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TopLeSpanBf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.UnfoldZn

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

def gam (hI : IsSplit P I) (n : Fin (Module.finrank ℝ (IR I)) → ℤ) : Vsp X.dim := ∑ j, n j • cp hI j

theorem gam_mem (hI : IsSplit P I) (n) : gam hI n ∈ X.L := by
  unfold gam
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (cp_mem hI j)

theorem gam_pair (hI : IsSplit P I) (n) (i) :
    (Hf (gam hI n) ((Ib hI i : IR I) : Vsp X.dim)).im = n i := by
  unfold gam
  rw [Col.Hf_sum_l, Complex.im_sum]
  simp_rw [← Int.cast_smul_eq_zsmul ℂ, Col.Hf_smul_l, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, zero_mul, add_zero, cp_pair hI, Pi.single_apply]
  simp

theorem pointNormSq_nonneg_quotient (hP : Ext.PackingCount) (hI : IsSplit P I) (β) (t) :
    0 ≤ (YB hI hP 1).ptN2 1 β t := by
  unfold GT.ptN2
  positivity

theorem fibre_sum (hI : IsSplit P I) (hP : Ext.PackingCount) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec 1 1) (W : Vsp X.dim) :
    ∫⁻ t in cubeIco (Fin (Module.finrank ℝ (IR I))), ENNReal.ofReal (X.ptN2 1 s fun _ => W + tb hI t) =
      ∑' n, ENNReal.ofReal ((YB hI hP 1).ptN2 1 (zmB hI s) (wmap (IR I) (W + gam hI n)) *
        Real.exp (-(2 * Real.pi) * ‖uc (IR I) (W + gam hI n)‖ ^ 2)) := by
  have hK : ∀ a ∈ IR I, ∀ b ∈ IR I, (Hf a b).im = 0 := Col.iso_IR hI.iso
  have hE2 : ∀ a : ℝ, Real.exp a ^ 2 = Real.exp (2 * a) := fun a => by
    rw [sq, ← Real.exp_add, two_mul]
  have hp1add : ∀ a b, Col.p1 (IR I) (a + b) = Col.p1 (IR I) a + Col.p1 (IR I) b := by
    intro a b
    simp only [Col.p1, z_add, add_smul, Finset.sum_add_distrib]
  have hp2add : ∀ a b, Col.p2 (IR I) (a + b) = Col.p2 (IR I) a + Col.p2 (IR I) b := by
    intro a b
    simp only [Col.p2, hp1add]
    abel
  have hp2K : ∀ b ∈ IR I, Col.p2 (IR I) b = 0 := by
    intro b hb
    have h := congrArg Subtype.val ((Col.ob (IR I)).sum_repr' ⟨b, hb⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    rw [Col.p2, Col.p1, sub_eq_zero]
    conv_lhs => rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [z_of_K hI k hb, Complex.coe_smul]
    rfl
  have hucn : ∀ v, ‖Col.uc (IR I) v‖ ^ 2 = ∑ k, (Col.z (IR I) k v).im ^ 2 := by
    intro v
    rw [← Col.Hf_self_re, Col.uc, Col.Hf_sum_l]
    simp [Col.Hf_sum_r, Col.Hf_rsmul_l, Col.Hf_rsmul_r, Col.Hf_e hK, Complex.re_sum, sq]
  have hnadd : ∀ a b : Vsp X.dim, ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * (Hf a b).re + ‖b‖ ^ 2 := by
    intro a b
    rw [← Col.Hf_self_re, ← Col.Hf_self_re, ← Col.Hf_self_re, Col.Hf_add_l, Col.Hf_add_r,
      Col.Hf_add_r, Col.Hf_swap a b]
    simp only [Complex.add_re, Complex.conj_re]
    ring
  set c : ℝ := Real.exp (-Real.pi * (2 * ∑ k, (Col.z (IR I) k W).im ^ 2 + ‖Col.p2 (IR I) W‖ ^ 2))
    with hc
  have hpt : ∀ t, X.ptN2 1 s (fun _ => W + tb hI t) = ‖zmG I s (W + tb hI t)‖ ^ 2 * c := by
    intro t
    have hw := Col.norm_sq_decomp hK (W + tb hI t)
    have hy : ∀ k, (Col.z (IR I) k (W + tb hI t)).im = (Col.z (IR I) k W).im := fun k => by
      rw [z_add, Complex.add_im, z_of_K hI k (tb_mem hI t), Complex.ofReal_im, add_zero]
    have hp : Col.p2 (IR I) (W + tb hI t) = Col.p2 (IR I) W := by
      rw [hp2add, hp2K _ (tb_mem hI t), add_zero]
    have key : ‖W + tb hI t‖ ^ 2 = (Col.S (IR I) (W + tb hI t)).re +
        2 * ∑ k, (Col.z (IR I) k W).im ^ 2 + ‖Col.p2 (IR I) W‖ ^ 2 := by
      rw [hw, hp]
      have : ∑ k, ‖Col.z (IR I) k (W + tb hI t)‖ ^ 2 =
          (Col.S (IR I) (W + tb hI t)).re + 2 * ∑ k, (Col.z (IR I) k W).im ^ 2 := by
        rw [Col.S, Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← hy k, Complex.sq_norm, Complex.normSq_apply, sq, Complex.mul_re]
        ring
      rw [this]
    have e1 : X.ptN2 1 s (fun _ => W + tb hI t) =
        ‖s (fun _ => W + tb hI t)‖ ^ 2 * Real.exp (-Real.pi * ‖W + tb hI t‖ ^ 2) := by
      unfold PT.ptN2 HC
      simp [Col.Hf_self_re]
    have e2 : ‖zmG I s (W + tb hI t)‖ ^ 2 = ‖s (fun _ => W + tb hI t)‖ ^ 2 *
        Real.exp (-Real.pi * (Col.S (IR I) (W + tb hI t)).re) := by
      unfold zmG
      rw [norm_mul, mul_pow, Complex.norm_exp, hE2]
      congr 2
      simp [Complex.mul_re]
      ring
    rw [e1, e2, mul_assoc, hc, ← Real.exp_add, key]
    congr 2
    ring
  have hcont : Continuous fun t : Fin (Module.finrank ℝ (IR I)) → ℝ => ‖zmG I s (W + tb hI t)‖ ^ 2 * c :=
    (((zmG_continuous hs).comp (continuous_const.add (tb_continuous hI))).norm.pow 2).mul continuous_const
  have hint : IntegrableOn (fun t : Fin (Module.finrank ℝ (IR I)) → ℝ => ‖zmG I s (W + tb hI t)‖ ^ 2 * c)
      (cubeIco (Fin (Module.finrank ℝ (IR I)))) := by
    refine (hcont.continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1))).mono_set ?_
    rw [cubeIco_eq]
    exact Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self
  have hpar : HasSum (fun n => ‖zmC hI s n W‖ ^ 2)
      (∫ t in {x : Fin (Module.finrank ℝ (IR I)) → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
        ‖zmG I s (W + tb hI t)‖ ^ 2) := fibre_parseval hI hs W
  have hcube : ∫ t in cubeIco (Fin (Module.finrank ℝ (IR I))), ‖zmG I s (W + tb hI t)‖ ^ 2 * c =
      (∑' n, ‖zmC hI s n W‖ ^ 2) * c := by
    rw [integral_mul_const, setIntegral_congr_set (cube_ae_eq _), hpar.tsum_eq]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun t => by positivity),
    hcube, ← tsum_mul_right,
    ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hpar.summable.mul_right c)]
  congr 1
  funext n
  congr 1
  have hγ := gam_mem hI n
  have hadd := zmC_add hI hs hγ n (gam_pair hI n) 0 W
  rw [zero_add] at hadd
  have hB : zmB hI s (Col.wmap (IR I) (W + gam hI n)) = zmC hI s 0 (W + gam hI n) := by
    unfold zmB
    rw [Col.jj_wmap' hK, ← zeroMode_proj_two hI hs]
  have heps : ‖(X.eps (gam hI n) : ℂ)‖ = 1 := by
    rcases X.eps_pm _ hγ with h | h <;> simp [h]
  have hg : (gaugeExp I (gam hI n) W).re =
      2 * Real.pi * ∑ k, (Col.z (IR I) k (gam hI n)).im * (Col.z (IR I) k W).im +
        Real.pi * ∑ k, (Col.z (IR I) k (gam hI n)).im * (Col.z (IR I) k (gam hI n)).im +
        Real.pi * (Hf (Col.p2 (IR I) W) (Col.p2 (IR I) (gam hI n))).re +
        Real.pi * ‖Col.p2 (IR I) (gam hI n)‖ ^ 2 / 2 := by
    unfold gaugeExp
    simp [Complex.mul_re, Complex.mul_im, Complex.re_sum, Col.Hf_self_re, Finset.mul_sum]
  have hp2n := hnadd (Col.p2 (IR I) W) (Col.p2 (IR I) (gam hI n))
  rw [← hp2add] at hp2n
  have hucW : ‖Col.uc (IR I) (W + gam hI n)‖ ^ 2 =
      ∑ k, ((Col.z (IR I) k W).im + (Col.z (IR I) k (gam hI n)).im) ^ 2 := by
    rw [hucn]
    simp [z_add]
  have hsq : ∑ k, ((Col.z (IR I) k W).im + (Col.z (IR I) k (gam hI n)).im) ^ 2 =
      ∑ k, (Col.z (IR I) k W).im ^ 2 +
        2 * ∑ k, (Col.z (IR I) k (gam hI n)).im * (Col.z (IR I) k W).im +
        ∑ k, (Col.z (IR I) k (gam hI n)).im * (Col.z (IR I) k (gam hI n)).im := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  unfold GT.ptN2
  rw [hB, hadd, Col.norm_wmap hK, norm_mul, norm_mul, heps, one_mul, Complex.norm_exp, mul_pow, hE2,
    hp2n, hucW, hsq, hg, hc]
  rw [mul_comm (Real.exp _) (‖zmC hI s n W‖ ^ 2), mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 2
  push_cast
  ring

theorem YB_cube (hI : IsSplit P I) (hP : Ext.PackingCount) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec 1 1) (A0 : EuclideanSpace ℂ (Fin (gB (IR I)))) :
    ∫⁻ r in cubeIco (Fin (2 * Fintype.card (Fin (gB (IR I))))),
        ENNReal.ofReal ((YB hI hP 1).ptN2 1 (zmB hI s) (A0 + (bB hI hP).equivFun.symm r)) =
      ENNReal.ofReal ((YB hI hP 1).l2 1 (zmB hI s)) := by
  have hF : zmB hI s ∈ (Col.YB hI hP 1).Sec 1 := zeroMode_mem_sections hI hP hs
  have hE : ∀ a b : ℝ, Real.exp a ^ 2 * Real.exp b = Real.exp (2 * a + b) := fun a b => by
    rw [Real.exp_add, sq, ← Real.exp_add, two_mul]
  have hper : ∀ γ ∈ lat (Col.YB hI hP 1).b, ∀ v,
      (Col.YB hI hP 1).ptN2 1 (zmB hI s) (v + γ) = (Col.YB hI hP 1).ptN2 1 (zmB hI s) v := by
    intro γ hγ v
    have h1 := hF.2 γ hγ v
    have hka := (Col.YB hI hP 1).ka_abs γ hγ
    have hn : ‖v + γ‖ ^ 2 = ‖v‖ ^ 2 + 2 * (Hf v γ).re + ‖γ‖ ^ 2 := by
      rw [← Col.Hf_self_re, ← Col.Hf_self_re, ← Col.Hf_self_re, Col.Hf_add_l, Col.Hf_add_r,
        Col.Hf_add_r, Col.Hf_swap v γ]
      simp only [Complex.add_re, Complex.conj_re]
      ring
    have hre : ((((1 : ℕ) : ℂ) * (Real.pi : ℂ) * Hf v γ + ((1 : ℕ) : ℂ) * (Real.pi : ℂ) * Hf γ γ / 2)).re =
        Real.pi * (Hf v γ).re + Real.pi * ‖γ‖ ^ 2 / 2 := by
      rw [← Col.Hf_self_re]
      simp [Complex.add_re, Complex.mul_re]
    unfold GT.ptN2
    rw [h1, norm_mul, norm_mul, hka, one_mul, Complex.norm_exp, hre, mul_pow, mul_right_comm, hE, hn,
      mul_comm]
    congr 2
    push_cast
    ring
  have hBsymm : ∀ x : Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ,
      (Col.bB hI hP).equivFun.symm x = ∑ i, x i • (Col.bB hI hP) i := fun x =>
    Module.Basis.equivFun_symm_apply _ _
  have hBc : Continuous (Col.bB hI hP).equivFun.symm :=
    (Col.bB hI hP).equivFun.symm.toLinearMap.continuous_of_finiteDimensional
  have hcont : Continuous ((Col.YB hI hP 1).ptN2 1 (zmB hI s)) := by
    unfold GT.ptN2
    exact (hF.1.continuous.norm.pow 2).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  set g : (Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ) → ℝ :=
    fun x => (Col.YB hI hP 1).ptN2 1 (zmB hI s) ((Col.bB hI hP).equivFun.symm x) with hgdef
  have hgc : Continuous g := hcont.comp hBc
  have hgper : ∀ (x : Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ)
      (n : Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℤ), g (x + fun i => (n i : ℝ)) = g x := by
    intro x n
    simp only [hgdef, map_add]
    apply hper
    rw [hBsymm]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  set a0 := (Col.bB hI hP).equivFun A0 with ha0
  have hshift : ∀ x, (Col.YB hI hP 1).ptN2 1 (zmB hI s) (A0 + (Col.bB hI hP).equivFun.symm x) =
      g (x + a0) := by
    intro x
    simp only [hgdef, map_add, ha0, LinearEquiv.symm_apply_apply]
    rw [add_comm]
  have hbox : ∫ x in {x : Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
      g (x + a0) = ∫ x in {x : Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
      g x := by
    have h := tof_box_shift (fun x => (g x : ℂ)) (Complex.continuous_ofReal.comp hgc)
      (fun x n => by simp only [hgper]) a0
    rw [integral_complex_ofReal, integral_complex_ofReal] at h
    exact_mod_cast h
  have hcube : ∫ x in cubeIco (Fin (2 * Fintype.card (Fin (gB (IR I))))), g (x + a0) =
      ∫ x in cubeIco (Fin (2 * Fintype.card (Fin (gB (IR I))))), g x := by
    rw [setIntegral_congr_set (cube_ae_eq _), setIntegral_congr_set (cube_ae_eq _)]
    exact hbox
  have hint : IntegrableOn (fun x => g (x + a0)) (cubeIco (Fin (2 * Fintype.card (Fin (gB (IR I)))))) := by
    refine ((hgc.comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1))).mono_set ?_
    rw [cubeIco_eq]
    exact Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self
  have hl2 : (Col.YB hI hP 1).l2 1 (zmB hI s) =
      ∫ x in cubeIco (Fin (2 * Fintype.card (Fin (gB (IR I))))), g (x + a0) := by
    unfold GT.l2
    rw [avg_fd_cube, hcube]
    rfl
  simp_rw [hshift]
  rw [hl2, ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => by simp only [hgdef]; unfold GT.ptN2; positivity)]

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
