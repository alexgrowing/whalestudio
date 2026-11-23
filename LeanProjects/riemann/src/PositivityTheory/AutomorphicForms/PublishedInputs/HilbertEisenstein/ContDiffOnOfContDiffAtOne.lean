import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.RightBilinearApply
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HasFDerivAtIntegralSchwartzBilin
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.PolyVHasTemperateGrowth
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ExistsDecayBoundTwo
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SigmaFinitePosRealMeasure
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.PFinInfGLMulVec
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.AestronglyMeasurableColumnWeight
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.PFinModuleSectionInv
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.IsFiniteMeasureRestrictFd

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff Topology
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

set_option linter.unusedSectionVars false

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem norm_vecMul_le (w : Vr F) (x : UpperTheory.V.TR.Lie F 2) : ‖w ᵥ* Matrix.of x‖ ≤ 2 * ‖w‖ * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply]
  have h0 : ‖x 0 j‖ ≤ ‖x‖ := (norm_le_pi_norm (x 0) j).trans (norm_le_pi_norm x 0)
  have h1 : ‖x 1 j‖ ≤ ‖x‖ := (norm_le_pi_norm (x 1) j).trans (norm_le_pi_norm x 1)
  calc ‖w 0 * x 0 j + w 1 * x 1 j‖ ≤ ‖w 0‖ * ‖x 0 j‖ + ‖w 1‖ * ‖x 1 j‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ ‖w‖ * ‖x‖ + ‖w‖ * ‖x‖ :=
        add_le_add (mul_le_mul (norm_le_pi_norm w 0) h0 (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul (norm_le_pi_norm w 1) h1 (norm_nonneg _) (norm_nonneg _))
    _ = 2 * ‖w‖ * ‖x‖ := by ring

theorem norm_mulVec_le (w : Vr F) (x : UpperTheory.V.TR.Lie F 2) : ‖Matrix.of x *ᵥ w‖ ≤ 2 * ‖w‖ * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply]
  have h0 : ‖x i 0‖ ≤ ‖x‖ := (norm_le_pi_norm (x i) 0).trans (norm_le_pi_norm x i)
  have h1 : ‖x i 1‖ ≤ ‖x‖ := (norm_le_pi_norm (x i) 1).trans (norm_le_pi_norm x i)
  calc ‖x i 0 * w 0 + x i 1 * w 1‖ ≤ ‖x i 0‖ * ‖w 0‖ + ‖x i 1‖ * ‖w 1‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ ‖x‖ * ‖w‖ + ‖x‖ * ‖w‖ :=
        add_le_add (mul_le_mul h0 (norm_le_pi_norm w 0) (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul h1 (norm_le_pi_norm w 1) (norm_nonneg _) (norm_nonneg _))
    _ = 2 * ‖w‖ * ‖x‖ := by ring

theorem half_norm_le_norm_left_bilinear {x : UpperTheory.V.TR.Lie F 2} (hx : x ∈ Metric.ball (UpperTheory.V.TR.oneL F 2) (1 / 4)) (v : Vr F) :
    (1 / 2 : ℝ) * ‖v‖ ≤ ‖B1 v x‖ := by
  have hx' : ‖x - UpperTheory.V.TR.oneL F 2‖ < 1 / 4 := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  set r := v ᵥ* Matrix.of (x - UpperTheory.V.TR.oneL F 2)
  have e : B1 v x = v + r := by
    rw [left_bilinear_apply]
    have : Matrix.of (x - UpperTheory.V.TR.oneL F 2) = Matrix.of x - 1 := rfl
    simp only [r, this, Matrix.vecMul_sub, Matrix.vecMul_one]
    abel
  have h2 : ‖r‖ ≤ 2 * ‖v‖ * ‖x - UpperTheory.V.TR.oneL F 2‖ := norm_vecMul_le v _
  have h3 : ‖v‖ ≤ ‖v + r‖ + ‖r‖ := by
    have := norm_sub_le (v + r) r
    rwa [add_sub_cancel_right] at this
  have h4 : ‖v‖ * ‖x - UpperTheory.V.TR.oneL F 2‖ ≤ ‖v‖ * (1 / 4) := mul_le_mul_of_nonneg_left hx'.le (norm_nonneg v)
  rw [e]
  nlinarith [norm_nonneg v]

theorem half_norm_le_norm_right_bilinear {x : UpperTheory.V.TR.Lie F 2} (hx : x ∈ Metric.ball (UpperTheory.V.TR.oneL F 2) (1 / 4)) (v : Vr F) :
    (1 / 2 : ℝ) * ‖v‖ ≤ ‖B2 v x‖ := by
  have hx' : ‖x - UpperTheory.V.TR.oneL F 2‖ < 1 / 4 := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  set r := Matrix.of (x - UpperTheory.V.TR.oneL F 2) *ᵥ v
  have e : B2 v x = v + r := by
    rw [right_bilinear_apply]
    have : Matrix.of (x - UpperTheory.V.TR.oneL F 2) = Matrix.of x - 1 := rfl
    simp only [r, this, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have h2 : ‖r‖ ≤ 2 * ‖v‖ * ‖x - UpperTheory.V.TR.oneL F 2‖ := norm_mulVec_le v _
  have h3 : ‖v‖ ≤ ‖v + r‖ + ‖r‖ := by
    have := norm_sub_le (v + r) r
    rwa [add_sub_cancel_right] at this
  have h4 : ‖v‖ * ‖x - UpperTheory.V.TR.oneL F 2‖ ≤ ‖v‖ * (1 / 4) := mul_le_mul_of_nonneg_left hx'.le (norm_nonneg v)
  rw [e]
  nlinarith [norm_nonneg v]

theorem invL_val (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    invL (UpperTheory.V.TR.toL y.val) = UpperTheory.V.TR.toL (y⁻¹).val := by
  simp only [invL, UpperTheory.V.TR.toL, Equiv.apply_symm_apply]
  rw [Matrix.coe_units_inv]

theorem invL_one : invL (UpperTheory.V.TR.oneL F 2) = UpperTheory.V.TR.oneL F 2 := by
  simp [invL, UpperTheory.V.TR.oneL, UpperTheory.V.TR.toL]

theorem contDiffAt_invL : ContDiffAt ℝ ∞ (invL (F := F)) (UpperTheory.V.TR.oneL F 2) := by
  have hdet : ContDiffAt ℝ ∞ (fun x : UpperTheory.V.TR.Lie F 2 => Ring.inverse (Matrix.of x).det)
      (UpperTheory.V.TR.oneL F 2) := by
    have hx : (Matrix.of (UpperTheory.V.TR.oneL F 2)).det = ((1 : (UpperTheory.V.TR.Rinf F)ˣ) : UpperTheory.V.TR.Rinf F) := by
      simp [UpperTheory.V.TR.oneL, UpperTheory.V.TR.toL]
    refine ContDiffAt.comp (g := Ring.inverse) (UpperTheory.V.TR.oneL F 2) ?_
      (UpperTheory.V.TR.contDiff_det (E := F) (a := 2)).contDiffAt
    rw [hx]
    exact contDiffAt_ringInverse (𝕜 := ℝ) (1 : (UpperTheory.V.TR.Rinf F)ˣ)
  have e : invL (F := F) = fun x => fun i j => Ring.inverse (Matrix.of x).det * Matrix.adjugate (Matrix.of x) i j := by
    funext x i j
    simp [invL, Matrix.inv_def, UpperTheory.V.TR.toL]
  rw [e]
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => hdet.mul ?_
  have hp : ∀ a b : Fin 2, ContDiff ℝ ∞ fun x : UpperTheory.V.TR.Lie F 2 => x a b := fun a b =>
    (contDiff_apply ℝ (UpperTheory.V.TR.Rinf F) b).comp (contDiff_apply ℝ (Fin 2 → UpperTheory.V.TR.Rinf F) a)
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta,
      Fin.mk_one] <;>
    first
    | exact (hp _ _).contDiffAt
    | exact (hp _ _).neg.contDiffAt

theorem dl_eq (g : GA F 2) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F))
    (hy : ∀ v, 0 < (Matrix.det (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) v) :
    absD (g * UpperTheory.V.TR.infGL F 2 y) = dl g (UpperTheory.V.TR.toL y.val) := by
  rw [absD_mul, absD_infGL, dl]
  congr 1
  exact Finset.prod_congr rfl fun v _ => abs_of_pos (hy v)

theorem contDiff_dl (g : GA F 2) : ContDiff ℝ ∞ (dl (F := F) g) :=
  contDiff_const.mul (contDiff_prod fun v _ =>
    (contDiff_apply ℝ ℝ v).comp (UpperTheory.V.TR.contDiff_det (E := F) (a := 2)))

theorem dl_one (g : GA F 2) : dl g (UpperTheory.V.TR.oneL F 2) = absD g := by
  simp [dl, UpperTheory.V.TR.oneL, UpperTheory.V.TR.toL]

theorem eis_decomp (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) {C : ℂ}
    (hC : ∀ h : GA F 2, thetaS (Phi c) h = C * ((absD h)⁻¹ : ℝ) * thetaT (PhiH c) h)
    (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F))
    (h1 : Integrable (fun q => kap1 χ c g q * archS F (B1 (w1 g q) (UpperTheory.V.TR.toL y.val)))
      (μS F {t | 1 ≤ (t : ℝ)}))
    (h2 : Integrable (fun q => kap2 χ c g q * archS F (B2 (w2 g q) (UpperTheory.V.TR.toL (y⁻¹).val)))
      (μS F {t | (t : ℝ) < 1})) :
    Eis χ (Phi c) (g * UpperTheory.V.TR.infGL F 2 y) =
      ((absD (g * UpperTheory.V.TR.infGL F 2 y) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
          ∫ q, kap1 χ c g q * archS F (B1 (w1 g q) (UpperTheory.V.TR.toL y.val)) ∂μS F {t | 1 ≤ (t : ℝ)} +
        C * (((absD (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : ℝ) : ℂ) *
          ((absD (g * UpperTheory.V.TR.infGL F 2 y) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
          ∫ q, kap2 χ c g q * archS F (B2 (w2 g q) (UpperTheory.V.TR.toL (y⁻¹).val)) ∂μS F {t | (t : ℝ) < 1} := by
  set g' := g * UpperTheory.V.TR.infGL F 2 y
  set Dc : ℂ := ((absD g' ^ ((1 : ℝ) / 2) : ℝ) : ℂ)
  set Ac : ℂ := (((absD g')⁻¹ : ℝ) : ℂ)
  set S1 : Set {r : ℝ // 0 < r} := {t | 1 ≤ (t : ℝ)}
  set S2 : Set {r : ℝ // 0 < r} := {t | (t : ℝ) < 1}
  have hS2 : S2 = S1ᶜ := by
    ext t
    simp [S1, S2]
  obtain ⟨hi1, he1⟩ := integral_iter_eq S1 measurableSet_ge_one h1
  obtain ⟨hi2, he2⟩ := integral_iter_eq S2 measurableSet_lt_one h2
  set G : {r : ℝ // 0 < r} → ℂ := fun t => ∫ u in normOneFundamentalDomain F, eisInt χ (Phi c) g' t u ∂normOneMeasure F
  have eG1 : G = fun t => (∫ u in normOneFundamentalDomain F, ∑' ξ : Xi F,
      kap1 χ c g ((t, u), ξ) * archS F (B1 (w1 g ((t, u), ξ)) (UpperTheory.V.TR.toL y.val)) ∂normOneMeasure F) * Dc := by
    funext t
    simp only [G, g', eisInt_row]
    exact integral_mul_const _ _
  have eG2 : G = fun t => C * Ac * Dc * ∫ u in normOneFundamentalDomain F, ∑' ξ : Xi F,
      kap2 χ c g ((t, u), ξ) * archS F (B2 (w2 g ((t, u), ξ)) (UpperTheory.V.TR.toL (y⁻¹).val)) ∂normOneMeasure F := by
    funext t
    simp only [G, g', eisInt_col χ c g hC]
    exact integral_const_mul _ _
  have hG1 : IntegrableOn G S1 posRealMeasure := by
    rw [eG1]
    exact hi1.mul_const _
  have hG2 : IntegrableOn G S1ᶜ posRealMeasure := by
    rw [eG2, ← hS2]
    exact hi2.const_mul _
  have hG : Integrable G posRealMeasure := by
    have := hG1.union hG2
    rwa [Set.union_compl_self, integrableOn_univ] at this
  change ∫ t, G t ∂posRealMeasure = _
  rw [← integral_add_compl measurableSet_ge_one hG]
  congr 1
  · rw [eG1, integral_mul_const, he1, mul_comm]
  · rw [eG2, ← hS2, integral_const_mul, he2]

theorem contDiffAt_chart_one (hP : SPois) (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (H : Hyp χ c)
    (g : GA F 2) : ContDiffAt ℝ ∞ (UpperTheory.V.TR.chart (Eis χ (Phi c)) g) (UpperTheory.V.TR.oneL F 2) := by
  obtain ⟨C, hC⟩ := hP F χ c H
  have hC' : ∀ h : GA F 2, thetaS (Phi c) h = C * ((absD h)⁻¹ : ℝ) * thetaT (PhiH c) h :=
    fun h => (hC h).2.2
  set U : Set (UpperTheory.V.TR.Lie F 2) := Metric.ball (UpperTheory.V.TR.oneL F 2) (1 / 4)
  have hU : IsOpen U := Metric.isOpen_ball
  have h1U : UpperTheory.V.TR.oneL F 2 ∈ U := Metric.mem_ball_self (by norm_num)
  have m1 := aestronglyMeasurable_first_kernel χ c g {t | 1 ≤ (t : ℝ)}
  have mw1 := aestronglyMeasurable_row_weight (F := F) g {t | 1 ≤ (t : ℝ)}
  have m2 := aestronglyMeasurable_second_kernel χ c g {t | (t : ℝ) < 1}
  have mw2 := aestronglyMeasurable_column_weight (F := F) g {t | (t : ℝ) < 1}
  obtain ⟨k1, hk1⟩ := hint1 H g m1 mw1
  obtain ⟨k2, hk2⟩ := hint2 H g m2 mw2
  have hc : (0 : ℝ) < 1 / 2 := by norm_num
  set I1 : UpperTheory.V.TR.Lie F 2 → ℂ := fun x =>
    ∫ q, kap1 χ c g q * archS F (B1 (w1 g q) x) ∂μS F {t | 1 ≤ (t : ℝ)}
  set I2 : UpperTheory.V.TR.Lie F 2 → ℂ := fun z =>
    ∫ q, kap2 χ c g q * archS F (B2 (w2 g q) z) ∂μS F {t | (t : ℝ) < 1}
  have hI1 : ContDiffOn ℝ ∞ I1 U :=
    contDiffOn_integral_schwartz_bilin (archS F) B1 hU hc (fun x hx v => half_norm_le_norm_left_bilinear hx v) m1 mw1 hk1
  have hI2 : ContDiffOn ℝ ∞ I2 U :=
    contDiffOn_integral_schwartz_bilin (archS F) B2 hU hc (fun x hx v => half_norm_le_norm_right_bilinear hx v) m2 mw2 hk2
  have hI1a : ContDiffAt ℝ ∞ I1 (UpperTheory.V.TR.oneL F 2) := hI1.contDiffAt (hU.mem_nhds h1U)
  have hI2a : ContDiffAt ℝ ∞ (fun x => I2 (invL x)) (UpperTheory.V.TR.oneL F 2) :=
    by
      refine ContDiffAt.comp (g := I2) (UpperTheory.V.TR.oneL F 2) ?_ contDiffAt_invL
      rw [invL_one]
      exact hI2.contDiffAt (hU.mem_nhds h1U)
  have hdl := (contDiff_dl (F := F) g).contDiffAt (x := UpperTheory.V.TR.oneL F 2)
  have hdl0 : dl g (UpperTheory.V.TR.oneL F 2) ≠ 0 := by rw [dl_one]; exact (absD_pos g).ne'
  have hD : ContDiffAt ℝ ∞ (fun x => ((dl g x ^ ((1 : ℝ) / 2) : ℝ) : ℂ)) (UpperTheory.V.TR.oneL F 2) :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp _ (hdl.rpow_const_of_ne hdl0)
  have hA : ContDiffAt ℝ ∞ (fun x => (((dl g x)⁻¹ : ℝ) : ℂ)) (UpperTheory.V.TR.oneL F 2) :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp _ (hdl.inv hdl0)
  have hΦ : ContDiffAt ℝ ∞ (fun x => ((dl g x ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * I1 x +
      C * (((dl g x)⁻¹ : ℝ) : ℂ) * ((dl g x ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * I2 (invL x)) (UpperTheory.V.TR.oneL F 2) :=
    (hD.mul hI1a).add (((contDiffAt_const.mul hA).mul hD).mul hI2a)
  refine hΦ.congr_of_eventuallyEq ?_
  have hinv : ∀ᶠ x in 𝓝 (UpperTheory.V.TR.oneL F 2), invL x ∈ U :=
    contDiffAt_invL.continuousAt.preimage_mem_nhds (by rw [invL_one]; exact hU.mem_nhds h1U)
  have hunit : ∀ᶠ x in 𝓝 (UpperTheory.V.TR.oneL F 2), x ∈ UpperTheory.V.TR.invSet F 2 :=
    UpperTheory.V.TR.isOpen_invSet.mem_nhds (by simp [UpperTheory.V.TR.invSet, UpperTheory.V.TR.oneL, UpperTheory.V.TR.toL])
  have hdet : ∀ᶠ x in 𝓝 (UpperTheory.V.TR.oneL F 2), ∀ v, 0 < (Matrix.det (Matrix.of x)) v := by
    refine Filter.eventually_all.2 fun v => ?_
    have hcont : ContinuousAt (fun x : UpperTheory.V.TR.Lie F 2 => (Matrix.det (Matrix.of x)) v) (UpperTheory.V.TR.oneL F 2) :=
      ((continuous_apply v).comp (UpperTheory.V.TR.contDiff_det (E := F) (a := 2)).continuous).continuousAt
    exact continuousAt_const.eventually_lt hcont (by simp [UpperTheory.V.TR.oneL, UpperTheory.V.TR.toL])
  filter_upwards [hU.mem_nhds h1U, hinv, hunit, hdet] with x hxU hxi hxu hxd
  set y : GL (Fin 2) (UpperTheory.V.TR.Rinf F) := (show IsUnit (Matrix.of x) from hxu).unit
  have hy : UpperTheory.V.TR.toL y.val = x := rfl
  have hyi : UpperTheory.V.TR.toL (y⁻¹).val = invL x := by rw [← invL_val, hy]
  have hyd : absD (g * UpperTheory.V.TR.infGL F 2 y) = dl g x := by
    rw [dl_eq g y hxd, hy]
  have i1 := integrable_schwartz_bilin (archS F) B1 hc (fun x hx v => half_norm_le_norm_left_bilinear hx v) m1 mw1 hk1 hxU
  have i2 := integrable_schwartz_bilin (archS F) B2 hc (fun x hx v => half_norm_le_norm_right_bilinear hx v) m2 mw2 hk2 hxi
  rw [← hy] at i1
  rw [← hyi] at i2
  rw [← hy, UpperTheory.V.TR.chart_val, eis_decomp χ c g hC' y i1 i2, hyd, hyi, hy]

theorem contDiffOn_of_contDiffAt_one {φ : GA F 2 → ℂ}
    (h : ∀ g, ContDiffAt ℝ ∞ (UpperTheory.V.TR.chart φ g) (UpperTheory.V.TR.oneL F 2))
    (g : GA F 2) : ContDiffOn ℝ ∞ (UpperTheory.V.TR.chart φ g) (UpperTheory.V.TR.invSet F 2) := by
  intro x hx
  set y : GL (Fin 2) (UpperTheory.V.TR.Rinf F) := (show IsUnit (Matrix.of x) from hx).unit
  have hy : UpperTheory.V.TR.toL y.val = x := rfl
  have e : UpperTheory.V.TR.chart φ g =
      UpperTheory.V.TR.chart φ (g * UpperTheory.V.TR.infGL F 2 y) ∘ UpperTheory.V.TR.lmul (UpperTheory.V.TR.toL (y⁻¹).val) := by
    rw [← UpperTheory.V.TR.chart_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  rw [e]
  refine ContDiffAt.contDiffWithinAt ?_
  have h1 : UpperTheory.V.TR.lmul (UpperTheory.V.TR.toL (y⁻¹).val) x = UpperTheory.V.TR.oneL F 2 := by
    rw [← hy]
    change Matrix.of.symm (Matrix.of (UpperTheory.V.TR.toL (y⁻¹).val) * Matrix.of (UpperTheory.V.TR.toL y.val)) = _
    simp
  refine ContDiffAt.comp x ?_
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) (UpperTheory.V.TR.lmul (UpperTheory.V.TR.toL (y⁻¹).val))).contDiffAt
  rw [h1]
  exact h _

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

namespace UpperTheory.HilbertEisensteinWeightOne

theorem smoothness_holds : SPois → SInt → SSmooth := by
  intro hP _ F _ _ _ χ c H g
  exact EisensteinSmoothness.contDiffOn_of_contDiffAt_one (fun g => EisensteinSmoothness.contDiffAt_chart_one hP χ c H g) g

end UpperTheory.HilbertEisensteinWeightOne
