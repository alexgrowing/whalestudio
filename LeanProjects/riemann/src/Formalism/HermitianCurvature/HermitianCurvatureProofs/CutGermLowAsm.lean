import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLow
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermPartsCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinLeTruncatedExponential

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

theorem gl_isLocPt_snoc {a : C.LPt} {j m : ℕ} (ha : D.IsLocPt a j) (hm : 1 ≤ m) {c : ℂ} (hc : c ≠ 0) :
    D.IsLocPt (a ++ [(m, c)]) (j + m) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact ha.1 x hx
    · simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨hm, hc⟩
  · rw [← ha.2]
    simp [D.ptSize, List.map_append, List.sum_append]

theorem gl_fsv (σ z : ℂ) : P5.fsv σ z = G.psi (-U.betaU) (1 * σ * z) := by
  rw [TBBx1.fsv_eq]
  unfold G.psi U.betaU Formalism.QuantumDeterminants.cStd
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, Complex.one_im]
  push_cast
  ring

section vec

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem gl_inner_self (u : H) : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl

end vec

theorem germDataLowAll_of_parts (hGr : GLGram) (hFi : GLFibre) (hCo : GLCont) (hGe : GLGerm) : GermDataLowAll := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F Y K N Cb hCb hF hnn b s hb hs hbs hlev h hh w hw hN hBdd
  have hi : b + s - 1 ≤ P.r := hlev
  have hN' : w.length ≤ N := by omega
  obtain ⟨H, i1, i2, i3, Vec, hVec⟩ := hGr hA Wp Wq P p nn F Y N Cb hCb hF hnn (b + s - 1) hi w hw hN'
  let _ := i1; let _ := i2; have _ := i3
  have hs0 : s ≠ 0 := by omega
  have hpi : (0 : ℝ) < Real.pi ^ (s - 1) := pow_pos Real.pi_pos _
  set κ : ℝ := (Real.pi ^ (s - 1))⁻¹ with hκ
  have hκκ : Real.pi ^ (2 * (s - 1)) * (κ * κ) = 1 := by
    rw [hκ, pow_mul', sq, ← mul_inv, mul_inv_cancel₀ (by positivity)]
  let ut : ℂ → ℂ → H := fun x D => (((κ * ‖x‖ ^ (s - 1)) : ℝ) : ℂ) • Vec (h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)])
  let bt : ℂ → H := fun z => if z = 0 then 0 else ((((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • Vec (h ++ [(s, z)])

  have hcv : ∀ x : ℂ, x ≠ 0 → ∀ c : ℂ, PBK.cvec s ut x c = (κ : ℂ) • Vec ((h ++ [(s - 1, x⁻¹)]) ++ [(1, c)]) := by
    intro x hx c
    have ha : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
    have hn : (‖x‖ ^ (s - 1) : ℝ) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
    simp only [PBK.cvec, ut, smul_smul, List.append_assoc, List.cons_append, List.nil_append]
    rw [mul_div_cancel₀ c ha, ← Complex.ofReal_mul]
    congr 2
    field_simp

  have hj : b + s - 2 + 1 = b + s - 1 := by omega
  have hloc : ∀ t : ℂ, t ≠ 0 → D.IsLocPt (h ++ [(s - 1, t)]) (b + s - 2) := by
    intro t ht
    have := gl_isLocPt_snoc hh (by omega : 1 ≤ s - 1) ht
    rwa [show b - 1 + (s - 1) = b + s - 2 by omega] at this

  have hgram : ∀ x x' : ℂ, x ≠ 0 → x' ≠ 0 →
      ∫ c, ⟪PBK.cvec s ut x c, PBK.cvec s ut x' c⟫_ℂ =
        ((κ * κ : ℝ) : ℂ) * TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, x⁻¹)]) (h ++ [(s - 1, x'⁻¹)]) := by
    intro x x' hx hx'
    obtain ⟨-, hfib⟩ := hFi hA Wp Wq P p nn F Y N Cb hCb hF hnn (b + s - 2) (by omega) w hw hN'
      (h ++ [(s - 1, x⁻¹)]) (h ++ [(s - 1, x'⁻¹)]) (hloc _ (inv_ne_zero hx)) (hloc _ (inv_ne_zero hx'))
    rw [hj] at hfib
    rw [← hfib, ← integral_const_mul]
    congr 1
    funext c
    rw [hcv x hx c, hcv x' hx' c, GermFibreKernels.inner_real_smul_smul, hVec]

  have hbz : ∀ z : ℂ, z ≠ 0 → PBK.bz s bt z = Vec (h ++ [(s, z)]) := by
    intro z hz
    simp only [PBK.bz, bt, if_neg hz, smul_smul, ← Complex.ofReal_mul]
    rw [mul_inv_cancel₀, Complex.ofReal_one, one_smul]
    have : (0 : ℝ) < ‖z‖ ^ (s - 1) := pow_pos (norm_pos_iff.mpr hz) _
    have hs' : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs0
    positivity

  have hVecR : ∀ i (hi' : i = b + s - 1) a a', TBB.NP p nn F i w a a' = ⟪Vec a, Vec a'⟫_ℂ := by
    intro i hi' a a'; subst hi'; exact hVec a a'
  have hcont1 : ∀ t : ℂ, t ≠ 0 → ContinuousOn (fun c : ℂ => Vec ((h ++ [(s - 1, t)]) ++ [(1, c)])) {0}ᶜ := by
    intro t ht
    have hk := hCo hA Wp Wq P p nn F Y N Cb hCb hF hnn (b + s - 2) 1 le_rfl (by omega) w hw hN' _ (hloc t ht)
    exact GermFibreKernels.vec_continuousOn _ Vec (hVecR _ hj) (fun c => (h ++ [(s - 1, t)]) ++ [(1, c)]) {0}ᶜ hk
  have hcontS : ContinuousOn (fun z : ℂ => Vec (h ++ [(s, z)])) {0}ᶜ := by
    have hk := hCo hA Wp Wq P p nn F Y N Cb hCb hF hnn (b - 1) s (by omega) (by omega) w hw hN' h hh
    exact GermFibreKernels.vec_continuousOn _ Vec (hVecR _ (by omega)) (fun z => h ++ [(s, z)]) {0}ᶜ hk

  obtain ⟨B0, hB0⟩ := hBdd w (TBBx1.isExt_self hw hN')
  refine ⟨H, i1, i2, i3, ut, bt, -U.betaU, (-1) ^ (s + 1), 1, κ * κ * B0, Real.pi ^ (2 * (s - 1)), 1,
    zero_le_one, ?_, Or.inl rfl, ?_, gl_fsv, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    exact one_le_mul_of_one_le_of_one_le h1 (one_le_pow₀ h1)
  · have hae : ∀ᵐ z : ℂ ∂volume, z ∈ ({0}ᶜ : Set ℂ) :=
      measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : ℂ))
    have hmeas0 : MeasurableSet ({0}ᶜ : Set ℂ) := (measurableSet_singleton 0).compl
    refine ⟨hs0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold U.betaU Formalism.QuantumDeterminants.cStd
      simp [Complex.I_ne_zero]
    · simp [norm_pow]
    ·
      intro _ _ x hx
      refine (PBK.memLp_cvec s ut x hx).2 ?_
      have hfun : PBK.cvec s ut x = fun c => (κ : ℂ) • Vec ((h ++ [(s - 1, x⁻¹)]) ++ [(1, c)]) := funext (hcv x hx)
      rw [hfun]
      refine MemLp.const_smul ?_ _
      have hmeas : AEStronglyMeasurable (fun c : ℂ => Vec ((h ++ [(s - 1, x⁻¹)]) ++ [(1, c)])) volume := by
        have h2 := (hcont1 x⁻¹ (inv_ne_zero hx)).aestronglyMeasurable (μ := volume) hmeas0
        rwa [Measure.restrict_eq_self_of_ae_mem hae] at h2
      refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
      obtain ⟨hint, -⟩ := hFi hA Wp Wq P p nn F Y N Cb hCb hF hnn (b + s - 2) (by omega) w hw hN' _ _
        (hloc _ (inv_ne_zero hx)) (hloc _ (inv_ne_zero hx))
      rw [hj] at hint
      refine (Complex.reCLM.integrable_comp hint).congr (Eventually.of_forall fun c => ?_)
      simp only [Complex.reCLM_apply]
      rw [hVec, gl_inner_self, Complex.ofReal_re]
    ·
      intro _ _ x hx
      have e1 := PBK.cvec_inner s ut ut x x hx hx
      simp only [div_self (pow_ne_zero _ hx), norm_one, Complex.ofReal_one, one_smul, one_mul] at e1
      have e2 : ∫ D, ⟪ut x D, ut x D⟫_ℂ = ((∫ D, ‖ut x D‖ ^ 2 : ℝ) : ℂ) := by
        simp_rw [gl_inner_self]; exact integral_ofReal
      rw [e2, hgram x x hx hx] at e1
      have e3 := congrArg Complex.re e1
      rw [Complex.ofReal_re, Complex.re_ofReal_mul] at e3
      rw [← e3]
      have hE : (TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, x⁻¹)]) (h ++ [(s - 1, x⁻¹)])).re ≤ B0 :=
        hB0 ⟨⟨x⁻¹, inv_ne_zero hx⟩, rfl⟩
      exact mul_le_mul_of_nonneg_left hE (mul_self_nonneg κ)
    ·
      intro _ _
      let _ : MeasurableSpace H := borel H
      have _ : BorelSpace H := ⟨rfl⟩
      let g : ℂ → H := fun z => ((((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • Vec (h ++ [(s, z)])
      have hgc : ContinuousOn g {0}ᶜ := by
        refine ContinuousOn.smul ?_ hcontS
        refine Complex.continuous_ofReal.comp_continuousOn ?_
        refine ContinuousOn.inv₀ (Continuous.continuousOn (by fun_prop)) fun z hz => ?_
        have : (0 : ℝ) < ‖z‖ ^ (s - 1) := pow_pos (norm_pos_iff.mpr hz) _
        have hs' : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs0
        positivity
      have hbt' : bt = ({0}ᶜ : Set ℂ).piecewise g (fun _ => 0) := by
        funext z
        by_cases hz : z = 0
        · simp [bt, hz]
        · simp [bt, hz, Set.piecewise, g]
      show StronglyMeasurable bt
      rw [stronglyMeasurable_iff_measurable_separable, hbt']
      refine ⟨ContinuousOn.measurable_piecewise hgc continuousOn_const hmeas0, ?_⟩
      refine TopologicalSpace.IsSeparable.mono (s := g '' {0}ᶜ ∪ {0}) ?_ (Set.range_subset_iff.2 fun z => ?_)
      · exact (hgc.isSeparable_image (TopologicalSpace.IsSeparable.of_separableSpace _)).union
          (Set.finite_singleton (0 : H)).isSeparable
      · by_cases hz : z ∈ ({0}ᶜ : Set ℂ)
        · left; rw [Set.piecewise_eq_of_mem _ _ _ hz]; exact ⟨z, hz, rfl⟩
        · right; rw [Set.piecewise_eq_of_notMem _ _ _ hz]; rfl
    ·
      intro _ _ K' hK hK0
      have hsub : K' ⊆ {0}ᶜ := fun z hz hz0 => hK0 (by rw [Set.mem_singleton_iff.1 hz0] at hz; exact hz)
      have hc : ContinuousOn (fun z => ‖Vec (h ++ [(s, z)])‖ ^ 2) K' := (hcontS.norm.pow 2).mono hsub
      refine (hc.congr fun z hz => ?_).integrableOn_compact hK
      rw [hbz z (fun h0 => hK0 (h0 ▸ hz))]
    ·
      intro _ _ K' hK hK0
      obtain ⟨C, hC⟩ := hGe hA Wp Wq P p nn F Y N Cb hCb hF hnn b s hb hs hi h hh w hw hN' H Vec hVec K' hK hK0
      refine ⟨C, fun x hx => Eventually.of_forall fun D hD => ?_⟩
      have hD0 : D ≠ 0 := fun h0 => hK0 (h0 ▸ hD)
      refine le_of_eq_of_le ?_ (hC x hx D hD)
      congr 2
      unfold PBK.mainD
      refine Finset.sum_congr rfl fun z hz => ?_
      have hz0 : z ≠ 0 := by
        rintro rfl
        have hr := (Polynomial.mem_nthRoots (by omega : 0 < s)).1 (Multiset.mem_toFinset.1 hz)
        rw [zero_pow hs0] at hr
        exact hD0 (by simpa using hr.symm)
      exact congrArg (fun v => G.psi (-U.betaU) ((s : ℂ) * z * x) • v) (if_neg hz0)
  · intro t t' ht ht'
    have hg := hgram t⁻¹ t'⁻¹ (inv_ne_zero ht) (inv_ne_zero ht')
    simp only [inv_inv] at hg
    show _ = _ * ‖∫ c, ⟪PBK.cvec s ut t⁻¹ c, PBK.cvec s ut t'⁻¹ c⟫_ℂ‖
    rw [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_self_nonneg κ), ← mul_assoc, hκκ,
      one_mul]
  · intro z hz
    unfold TBB.Ew
    rw [hbz z hz, hVec, gl_inner_self, Complex.ofReal_re, one_mul]

end

end Formalism.FourierDecayAlt.P.CutBP
