import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

noncomputable section

open UpperHalfPlane hiding I
open MeasureTheory Complex Set
open scoped ComplexConjugate Real
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.HalfWt

theorem strip_transport (F : ℍ → ℂ) :
    (IntegrableOn F strip ↔ IntegrableOn
      (fun p : ℝ × ℝ => F (ofComplex ((p.1 : ℂ) + p.2 * I)) * (((p.2⁻¹) ^ 2 : ℝ) : ℂ))
      (Ico (0:ℝ) 1 ×ˢ Ioi (0:ℝ))) ∧
    ∫ z in strip, F z = ∫ p in Ico (0:ℝ) 1 ×ˢ Ioi (0:ℝ),
      F (ofComplex ((p.1 : ℂ) + p.2 * I)) * (((p.2⁻¹) ^ 2 : ℝ) : ℂ) := by
  have hemb : MeasurableEmbedding UpperHalfPlane.coe := UpperHalfPlane.measurableEmbedding_coe
  have hsym : MeasurePreserving Complex.measurableEquivRealProd.symm volume volume :=
    MeasurePreserving.symm Complex.measurableEquivRealProd Complex.volume_preserving_equiv_real_prod
  have hsymE : MeasurableEmbedding Complex.measurableEquivRealProd.symm :=
    Complex.measurableEquivRealProd.symm.measurableEmbedding
  have hT : MeasurableSet {w : ℂ | 0 ≤ w.re ∧ w.re < 1} :=
    (measurableSet_le measurable_const Complex.measurable_re).inter
      (measurableSet_lt Complex.measurable_re measurable_const)
  have hstrip : strip = UpperHalfPlane.coe ⁻¹' {w : ℂ | 0 ≤ w.re ∧ w.re < 1} := Set.ext fun z => Iff.rfl
  have hS : MeasurableSet strip := by
    rw [hstrip]
    exact UpperHalfPlane.measurable_coe hT
  have hc : ∀ p : ℝ × ℝ, Complex.measurableEquivRealProd.symm p = (p.1 : ℂ) + p.2 * I := by
    intro p
    apply Complex.ext <;> simp [Complex.measurableEquivRealProd_symm_apply]
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹'
      ({w : ℂ | 0 ≤ w.re ∧ w.re < 1} ∩ Set.range UpperHalfPlane.coe) = Ico (0:ℝ) 1 ×ˢ Ioi (0:ℝ) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_range, Set.mem_prod,
      Set.mem_Ico, Set.mem_Ioi, hc]
    constructor
    · rintro ⟨⟨h1, h2⟩, z, hz⟩
      refine ⟨⟨by simpa using h1, by simpa using h2⟩, ?_⟩
      have h : 0 < (z : ℂ).im := z.im_pos
      rw [hz] at h
      simpa using h
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨by simpa using h1, by simpa using h2⟩, ⟨(p.1 : ℂ) + p.2 * I, by simpa using h3⟩, rfl⟩
  have key_int : ∀ G : ℂ → ℂ, IntegrableOn (fun z : ℍ => G z) strip (Measure.comap UpperHalfPlane.coe volume) ↔
      IntegrableOn (fun p => G (Complex.measurableEquivRealProd.symm p)) (Ico (0:ℝ) 1 ×ˢ Ioi (0:ℝ)) := by
    intro G
    rw [hstrip, ← hpre]
    have h1 : IntegrableOn (fun z : ℍ => G z) (UpperHalfPlane.coe ⁻¹' {w : ℂ | 0 ≤ w.re ∧ w.re < 1})
        (Measure.comap UpperHalfPlane.coe volume) ↔
        IntegrableOn G {w : ℂ | 0 ≤ w.re ∧ w.re < 1} (Measure.map UpperHalfPlane.coe (Measure.comap UpperHalfPlane.coe volume)) :=
      (hemb.integrableOn_map_iff).symm
    rw [h1, hemb.map_comap, IntegrableOn, Measure.restrict_restrict hT]
    exact (hsym.integrableOn_comp_preimage hsymE).symm
  have key_integral : ∀ G : ℂ → ℂ, ∫ z in strip, G z ∂(Measure.comap UpperHalfPlane.coe volume) =
      ∫ p in Ico (0:ℝ) 1 ×ˢ Ioi (0:ℝ), G (Complex.measurableEquivRealProd.symm p) := by
    intro G
    rw [hstrip, ← hpre, ← hemb.setIntegral_map G, hemb.map_comap, Measure.restrict_restrict hT]
    exact (hsym.setIntegral_preimage_emb hsymE G _).symm
  set ρ : ℍ → NNReal := fun z => (1 / NNReal.mk z.im (le_of_lt z.im_pos)) ^ 2 with hρdef
  have hρ : Measurable ρ := by
    apply measurable_coe_nnreal_real_iff.mp
    have h : (fun z : ℍ => ((ρ z : NNReal) : ℝ)) = fun z : ℍ => (1 / (z : ℂ).im) ^ 2 := by
      funext z
      simp [hρdef]
    rw [h]
    exact (measurable_const.div (Complex.measurable_im.comp UpperHalfPlane.measurable_coe)).pow_const 2
  have hvol : (volume : Measure ℍ) =
      (Measure.comap UpperHalfPlane.coe volume).withDensity (fun z => ((ρ z : NNReal) : ENNReal)) :=
    UpperHalfPlane.volume_def
  set g : ℂ → ℂ := fun w => F (ofComplex w) * (((w.im⁻¹) ^ 2 : ℝ) : ℂ) with hg
  have hfun : (fun z : ℍ => ρ z • F z) = fun z : ℍ => g (z : ℂ) := by
    funext z
    simp only [hg, hρdef, UpperHalfPlane.ofComplex_apply, NNReal.smul_def, Complex.real_smul, NNReal.coe_pow,
      NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk, UpperHalfPlane.coe_im]
    push_cast
    ring
  have hfun2 : (fun p : ℝ × ℝ => g (Complex.measurableEquivRealProd.symm p)) =
      fun p : ℝ × ℝ => F (ofComplex ((p.1 : ℂ) + p.2 * I)) * (((p.2⁻¹) ^ 2 : ℝ) : ℂ) := by
    funext p
    rw [hg, hc p]
    simp only []
    congr 1
    simp
  constructor
  · rw [IntegrableOn, hvol, restrict_withDensity hS, integrable_withDensity_iff_integrable_smul hρ, hfun, ← hfun2]
    exact key_int g
  · rw [hvol, restrict_withDensity hS, integral_withDensity_eq_integral_smul hρ, hfun, ← hfun2]
    exact key_integral g

theorem FF_bound (hB1 : B1) (hB2 : B2) (k N M ν : ℕ) [NeZero N] [NeZero M] (hM : 2 ≤ M) (χ : DirichletCharacter ℂ N)
    (f : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ)) (a : ℕ → ℂ) (hf : IsForm k N χ f a)
    (ψ : DirichletCharacter ℂ M) (hν : ν ≤ 1) (s : ℂ) (hs : 2 < s.re) :
    Continuous (FF f ψ k ν s) ∧ ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧
      ∀ z : ℍ, ‖FF f ψ k ν s z‖ * (z.im⁻¹) ^ 2 ≤ g z.im := by
  obtain ⟨-, C, hC1, -, hC3⟩ := hB1 k N χ f a hf
  haveI : Fact (1 < M) := ⟨by omega⟩
  have hP0 : (fun n : ℤ => ψ⁻¹ (n : ZMod M)) 0 = 0 := by
    show ψ⁻¹ ((0 : ℤ) : ZMod M) = 0
    rw [Int.cast_zero]
    exact MulChar.map_nonunit _ not_isUnit_zero
  have hP1 : ∀ n : ℤ, ‖(fun n : ℤ => ψ⁻¹ (n : ZMod M)) n‖ ≤ 1 :=
    fun n => DirichletCharacter.norm_le_one _ _
  obtain ⟨hcont, -, -, C', hC'⟩ := hB2 (fun n : ℤ => ψ⁻¹ (n : ZMod M)) ν hν hP0 hP1
  have hC0 : 0 ≤ C := by
    have h := hC1 UpperHalfPlane.I
    rw [UpperHalfPlane.I_im, Real.one_rpow, mul_one] at h
    exact (norm_nonneg _).trans h
  have hC'0 : 0 ≤ C' := by
    have h := hC' UpperHalfPlane.I
    rw [UpperHalfPlane.I_im, Real.one_rpow, mul_one] at h
    exact (norm_nonneg _).trans h
  have hf_cont : Continuous (fun z : ℍ => f z) := (ModularFormClass.holo f).continuous
  have him : Continuous (fun z : ℍ => ((z.im : ℂ)) ^ om k ν s) :=
    (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).cpow continuous_const
      (fun z => Complex.ofReal_mem_slitPlane.mpr z.im_pos)
  refine ⟨?_, fun y => C * C' * (Set.indicator (Ioc (0:ℝ) 1) (fun y => y ^ (s.re / 2 - 2)) y +
      Real.exp (-y) * y ^ ((s.re + k) / 2 - 2)), ?_, ?_⟩
  · show Continuous (fun z : ℍ => f z * conj (th (fun n : ℤ => ψ⁻¹ (n : ZMod M)) ν (z : ℂ)) * (z.im : ℂ) ^ om k ν s)
    exact (hf_cont.mul (Complex.continuous_conj.comp hcont)).mul him
  · have hA0 : IntegrableOn (fun y : ℝ => y ^ (s.re / 2 - 2)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    have hA : Integrable (Set.indicator (Ioc (0:ℝ) 1) (fun y : ℝ => y ^ (s.re / 2 - 2))) (volume.restrict (Ioi 0)) :=
      (integrable_indicator_iff measurableSet_Ioc).mpr (hA0.mono le_rfl Measure.restrict_le_self)
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hB : IntegrableOn (fun y : ℝ => Real.exp (-y) * y ^ ((s.re + k) / 2 - 2)) (Ioi 0) := by
      have h := Real.GammaIntegral_convergent (s := (s.re + k) / 2 - 1) (by linarith)
      rw [show (s.re + k) / 2 - 1 - 1 = (s.re + k) / 2 - 2 by ring] at h
      exact h
    exact (hA.fun_add hB).const_mul (C * C')
  · intro z
    dsimp only
    have hy : 0 < z.im := z.im_pos
    have hω : (om k ν s).re = (s.re + k + ν + 1) / 2 := by
      simp only [om, Complex.div_ofNat_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
    have hnorm : ‖FF f ψ k ν s z‖ = ‖f z‖ * ‖th (fun n : ℤ => ψ⁻¹ (n : ZMod M)) ν (z : ℂ)‖ *
        z.im ^ ((s.re + k + ν + 1) / 2) := by
      show ‖f z * conj (th (fun n : ℤ => ψ⁻¹ (n : ZMod M)) ν (z : ℂ)) * (z.im : ℂ) ^ om k ν s‖ = _
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_cpow_eq_rpow_re_of_pos hy, hω]
    have hinv : (z.im⁻¹) ^ 2 = z.im ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hy.le, Real.rpow_two, inv_pow]
    have hth := hC' z
    have hf1 := hC1 z
    have hA0 : 0 ≤ Set.indicator (Ioc (0:ℝ) 1) (fun y => y ^ (s.re / 2 - 2)) z.im :=
      Set.indicator_nonneg (fun y hy' => Real.rpow_nonneg hy'.1.le _) _
    have hB0 : 0 ≤ Real.exp (-z.im) * z.im ^ ((s.re + k) / 2 - 2) := by positivity
    have hC'y : 0 ≤ C' * z.im ^ (-((ν:ℝ) + 1) / 2) := mul_nonneg hC'0 (by positivity)
    rw [hnorm, hinv]
    rcases le_or_gt z.im 1 with h1 | h1
    · have hind : Set.indicator (Ioc (0:ℝ) 1) (fun y => y ^ (s.re / 2 - 2)) z.im = z.im ^ (s.re / 2 - 2) :=
        Set.indicator_of_mem (show z.im ∈ Ioc (0:ℝ) 1 from ⟨hy, h1⟩) _
      have hCy : 0 ≤ C * z.im ^ (-(k:ℝ) / 2) := mul_nonneg hC0 (by positivity)
      calc ‖f z‖ * ‖th (fun n : ℤ => ψ⁻¹ (n : ZMod M)) ν (z : ℂ)‖ * z.im ^ ((s.re + k + ν + 1) / 2) * z.im ^ (-2 : ℝ)
          ≤ (C * z.im ^ (-(k:ℝ) / 2)) * (C' * z.im ^ (-((ν:ℝ) + 1) / 2)) * z.im ^ ((s.re + k + ν + 1) / 2) *
              z.im ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul hf1 hth (norm_nonneg _) hCy)
              (by positivity)) (by positivity)
        _ = C * C' * z.im ^ (s.re / 2 - 2) := by
            rw [show s.re / 2 - 2 = (-(k:ℝ) / 2) + (-((ν:ℝ) + 1) / 2) + ((s.re + k + ν + 1) / 2) + (-2) by ring,
              Real.rpow_add hy, Real.rpow_add hy, Real.rpow_add hy]
            ring
        _ ≤ _ := by
            rw [hind, mul_add]
            linarith [mul_nonneg (mul_nonneg hC0 hC'0) hB0]
    · have hf3 := hC3 z h1.le
      have hCe : 0 ≤ C * Real.exp (-z.im) := mul_nonneg hC0 (by positivity)
      calc ‖f z‖ * ‖th (fun n : ℤ => ψ⁻¹ (n : ZMod M)) ν (z : ℂ)‖ * z.im ^ ((s.re + k + ν + 1) / 2) * z.im ^ (-2 : ℝ)
          ≤ (C * Real.exp (-z.im)) * (C' * z.im ^ (-((ν:ℝ) + 1) / 2)) * z.im ^ ((s.re + k + ν + 1) / 2) *
              z.im ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul hf3 hth (norm_nonneg _) hCe)
              (by positivity)) (by positivity)
        _ = C * C' * (Real.exp (-z.im) * z.im ^ ((s.re + k) / 2 - 2)) := by
            rw [show (s.re + k) / 2 - 2 = (-((ν:ℝ) + 1) / 2) + ((s.re + k + ν + 1) / 2) + (-2) by ring,
              Real.rpow_add hy, Real.rpow_add hy]
            ring
        _ ≤ _ := by
            rw [mul_add]
            linarith [mul_nonneg (mul_nonneg hC0 hC'0) hA0]

theorem coeff_summable (k M ν : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (a : ℕ → ℂ) (C : ℝ) (ha0 : a 0 = 0)
    (han : ∀ n : ℕ, ‖a n‖ ≤ C * (n : ℝ) ^ ((k : ℝ) / 2)) (s : ℂ) (hs : 2 < s.re) :
    Summable fun n : ℕ => ‖2 * (ψ (n : ZMod M) * a (n ^ 2)) * (n : ℂ) ^ ν‖ /
      (4 * π * (n : ℝ) ^ 2) ^ (om k ν s - 1).re := by
  have hC : 0 ≤ C := by
    have h1 := han 1
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at h1
    exact (norm_nonneg _).trans h1
  have he : 2 * (om k ν s - 1).re = s.re + k + ν - 1 := by
    simp only [om, Complex.sub_re, Complex.div_ofNat_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
    ring
  have hπ : (0:ℝ) < 4 * π := by positivity
  have hP : (0:ℝ) < (4 * π) ^ (om k ν s - 1).re := Real.rpow_pos_of_pos hπ _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((Real.summable_nat_rpow.mpr (show 1 - s.re < -1 by linarith)).mul_left
      (2 * C * ((4 * π) ^ (om k ν s - 1).re)⁻¹))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine le_trans (le_of_eq (by simp [ha0])) (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hC)
      (inv_nonneg.mpr hP.le)) (Real.rpow_nonneg (Nat.cast_nonneg 0) _))
  · have hx : (0:ℝ) < n := Nat.cast_pos.mpr hn
    have hD : (4 * π * (n:ℝ) ^ 2) ^ (om k ν s - 1).re
        = (4 * π) ^ (om k ν s - 1).re * (n:ℝ) ^ (s.re + k + ν - 1) := by
      rw [Real.mul_rpow hπ.le (by positivity), ← he, Real.rpow_mul hx.le]
      congr 1
      rw [← Real.rpow_natCast]
      norm_num
    have hψ : ‖ψ (n : ZMod M)‖ ≤ 1 := DirichletCharacter.norm_le_one ψ _
    have ha := han (n ^ 2)
    have hk : ((n ^ 2 : ℕ) : ℝ) ^ ((k:ℝ) / 2) = (n:ℝ) ^ (k:ℝ) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
      congr 1
      push_cast
      ring
    rw [hk] at ha
    have hnum : ‖2 * (ψ (n : ZMod M) * a (n ^ 2)) * (n : ℂ) ^ ν‖ ≤ 2 * C * (n:ℝ) ^ ((k:ℝ) + ν) := by
      rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Real.rpow_add hx, Real.rpow_natCast _ ν]
      have h2 : ‖(2:ℂ)‖ = 2 := by simp
      rw [h2]
      calc 2 * (‖ψ (n : ZMod M)‖ * ‖a (n ^ 2)‖) * (n:ℝ) ^ ν
          ≤ 2 * (1 * (C * (n:ℝ) ^ (k:ℝ))) * (n:ℝ) ^ ν := by gcongr
        _ = 2 * C * ((n:ℝ) ^ (k:ℝ) * (n:ℝ) ^ ν) := by ring
    have hY : (n:ℝ) ^ (s.re + k + ν - 1) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
    rw [hD]
    calc ‖2 * (ψ (n : ZMod M) * a (n ^ 2)) * (n : ℂ) ^ ν‖ / ((4 * π) ^ (om k ν s - 1).re * (n:ℝ) ^ (s.re + k + ν - 1))
        ≤ 2 * C * (n:ℝ) ^ ((k:ℝ) + ν) / ((4 * π) ^ (om k ν s - 1).re * (n:ℝ) ^ (s.re + k + ν - 1)) := by
          gcongr
      _ = 2 * C * ((4 * π) ^ (om k ν s - 1).re)⁻¹ * ((n:ℝ) ^ ((k:ℝ) + ν) / (n:ℝ) ^ (s.re + k + ν - 1)) := by
          field_simp
      _ = 2 * C * ((4 * π) ^ (om k ν s - 1).re)⁻¹ * (n:ℝ) ^ (1 - s.re) := by
          rw [← Real.rpow_sub hx]
          congr 2
          ring

theorem coeff_term (k M ν : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (a : ℕ → ℂ) (ha0 : a 0 = 0) (s : ℂ) (n : ℕ) :
    Gamma (om k ν s - 1) * (2 * (ψ (n : ZMod M) * a (n ^ 2)) * (n : ℂ) ^ ν) /
        (((4 * π * (n : ℝ) ^ 2 : ℝ)) : ℂ) ^ (om k ν s - 1) =
      2 * Gamma (om k ν s - 1) * (4 * π : ℂ) ^ (1 - om k ν s) *
        LSeries.term (fun n => ψ n * a (n ^ 2)) (s + k - 1) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ha0]
  · have hn0 : n ≠ 0 := hn.ne'
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
    have h4π : (4 * π : ℂ) ≠ 0 := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have h4 : (((4 * π * (n : ℝ) ^ 2 : ℝ)) : ℂ) ^ (om k ν s - 1)
        = (4 * π : ℂ) ^ (om k ν s - 1) * (n : ℂ) ^ (s + k + ν - 1) := by
      rw [show ((4 * π * (n : ℝ) ^ 2 : ℝ) : ℂ) = ((4 * π : ℝ) : ℂ) * (((n ^ 2 : ℕ) : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
      congr 1
      · push_cast
        rfl
      · rw [Complex.ofReal_natCast, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
        congr 1
        simp only [om]
        push_cast
        ring
    have e1 : (4 * π : ℂ) ^ (1 - om k ν s) = ((4 * π : ℂ) ^ (om k ν s - 1))⁻¹ := by
      rw [← Complex.cpow_neg]
      congr 1
      ring
    have e2 : (n : ℂ) ^ (s + k + ν - 1) = (n : ℂ) ^ ν * (n : ℂ) ^ (s + k - 1) := by
      rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hnC]
      congr 1
      ring
    have hA : (4 * π : ℂ) ^ (om k ν s - 1) ≠ 0 := fun h => h4π ((Complex.cpow_eq_zero_iff _ _).mp h).1
    have hB : (n : ℂ) ^ (s + k - 1) ≠ 0 := fun h => hnC ((Complex.cpow_eq_zero_iff _ _).mp h).1
    have hC : (n : ℂ) ^ ν ≠ 0 := pow_ne_zero _ hnC
    rw [LSeries.term_of_ne_zero hn0, h4, e1, e2]
    field_simp

theorem strip_integral : B1 → B2 → HorizontalIntegralTwisted → U2 := by
  intro hB1 hB2 hU2a k N M ν _ _ hM hk χ f a hf ψ hν hψ s hs
  obtain ⟨ha0, C, -, han, -⟩ := hB1 k N χ f a hf
  obtain ⟨hcont, g, hg_int, hg_bd⟩ := FF_bound hB1 hB2 k N M ν hM χ f a hf ψ hν s hs
  have hA : (0:ℝ) < (om k ν s - 1).re := by
    have h2 : 2 * (om k ν s - 1).re = s.re + k + ν - 1 := by
      simp only [om, Complex.sub_re, Complex.div_ofNat_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
      ring
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hν0 : (0:ℝ) ≤ ν := Nat.cast_nonneg ν
    linarith
  have him : ∀ x y : ℝ, 0 < y → (ofComplex ((x:ℂ) + y * I)).im = y := by
    intro x y hy
    have h : 0 < ((x:ℂ) + y * I).im := by simpa using hy
    rw [ofComplex_apply_of_im_pos h]
    simp [UpperHalfPlane.im]
  have hSq : MeasurableSet (Ico (0:ℝ) 1 ×ˢ Ioi (0:ℝ)) := measurableSet_Ico.prod measurableSet_Ioi
  have hP : IntegrableOn (fun p : ℝ × ℝ => ((g p.2 : ℝ) : ℂ)) (Ico (0:ℝ) 1 ×ˢ Ioi (0:ℝ)) := by
    have h1 : Integrable (fun p : ℝ × ℝ => (1:ℂ) * ((g p.2 : ℝ) : ℂ))
        ((volume.restrict (Ico (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ)))) :=
      (integrable_const (1:ℂ)).mul_prod (Integrable.ofReal hg_int)
    have h2 : (fun p : ℝ × ℝ => (1:ℂ) * ((g p.2 : ℝ) : ℂ)) = fun p => ((g p.2 : ℝ) : ℂ) := by
      funext p
      exact one_mul _
    rw [h2] at h1
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact h1
  have hG : IntegrableOn (fun z : ℍ => ((g z.im * z.im ^ 2 : ℝ) : ℂ)) strip := by
    refine (strip_transport _).1.mpr (hP.congr_fun (fun p hp => ?_) hSq)
    have hy : 0 < p.2 := hp.2
    have hy' : p.2 ≠ 0 := hy.ne'
    dsimp only
    rw [him p.1 p.2 hy, ← Complex.ofReal_mul]
    congr 1
    field_simp
  have hFF : IntegrableOn (FF f ψ k ν s) strip := by
    refine Integrable.mono hG hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    have hy : 0 < z.im := z.im_pos
    have hy' : z.im ≠ 0 := hy.ne'
    have h1 := hg_bd z
    calc ‖FF f ψ k ν s z‖ = ‖FF f ψ k ν s z‖ * (z.im⁻¹) ^ 2 * z.im ^ 2 := by field_simp
      _ ≤ g z.im * z.im ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ ‖((g z.im * z.im ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact le_abs_self _
  refine ⟨hFF, ?_⟩
  rw [(strip_transport (FF f ψ k ν s)).2]
  have hH := (strip_transport (FF f ψ k ν s)).1.mp hFF
  set H : ℝ × ℝ → ℂ := fun p => FF f ψ k ν s (ofComplex ((p.1 : ℂ) + p.2 * I)) * (((p.2⁻¹) ^ 2 : ℝ) : ℂ)
    with hHdef
  have hH' : Integrable H ((volume.restrict (Ico (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hH
  rw [show (volume : Measure (ℝ × ℝ)).restrict (Ico (0:ℝ) 1 ×ˢ Ioi (0:ℝ)) =
      (volume.restrict (Ico (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ))) by
    rw [Measure.volume_eq_prod, Measure.prod_restrict], integral_prod_symm H hH']
  have hinner : ∀ y ∈ Ioi (0:ℝ), ∫ x in Ico (0:ℝ) 1, H (x, y) =
      (y : ℂ) ^ (om k ν s - 1 - 1) * ∑' n : ℕ, 2 * (ψ (n : ZMod M) * a (n ^ 2)) * (n : ℂ) ^ ν *
        ((Real.exp (-(4 * π * (n : ℝ) ^ 2 * y)) : ℝ) : ℂ) := by
    intro y hy
    have hy0 : 0 < y := hy
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
    have hpos : ∀ x : ℝ, 0 < ((x : ℂ) + y * I).im := fun x => by simpa using hy0
    have hpt : ∀ x : ℝ, FF f ψ k ν s (ofComplex ((x : ℂ) + y * I)) * (((y⁻¹) ^ 2 : ℝ) : ℂ) =
        (f ⟨(x : ℂ) + y * I, hpos x⟩ * conj (th (fun n : ℤ => ψ⁻¹ (n : ZMod M)) ν ((x : ℂ) + y * I))) *
          (y : ℂ) ^ (om k ν s - 1 - 1) := by
      intro x
      rw [ofComplex_apply_of_im_pos (hpos x)]
      show f ⟨(x : ℂ) + y * I, hpos x⟩ * conj (th (fun n : ℤ => ψ⁻¹ (n : ZMod M)) ν ((x : ℂ) + y * I)) *
          ((((x : ℂ) + y * I).im : ℝ) : ℂ) ^ om k ν s * (((y⁻¹) ^ 2 : ℝ) : ℂ) = _
      rw [show ((x : ℂ) + y * I).im = y by simp, Complex.cpow_sub _ _ hyC, Complex.cpow_sub _ _ hyC,
        Complex.cpow_one]
      push_cast
      ring
    simp only [hHdef]
    rw [setIntegral_congr_fun measurableSet_Ico (fun x _ => hpt x), integral_mul_const,
      integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one,
      ← (hU2a k N M ν hM χ f a hf ψ hν hψ y hy0).tsum_eq]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hinner]
  have hT : ∀ y : ℝ, (y : ℂ) ^ (om k ν s - 1 - 1) * ∑' n : ℕ, 2 * (ψ (n : ZMod M) * a (n ^ 2)) * (n : ℂ) ^ ν *
        ((Real.exp (-(4 * π * (n : ℝ) ^ 2 * y)) : ℝ) : ℂ) =
      ∑' n : ℕ, 2 * (ψ (n : ZMod M) * a (n ^ 2)) * (n : ℂ) ^ ν *
        ((y : ℂ) ^ (om k ν s - 1 - 1) * ((Real.exp (-(4 * π * (n : ℝ) ^ 2 * y)) : ℝ) : ℂ)) := by
    intro y
    rw [← tsum_mul_left]
    congr 1
    funext n
    ring
  simp_rw [hT]
  have hFint : ∀ n : ℕ, Integrable (fun y : ℝ => 2 * (ψ (n : ZMod M) * a (n ^ 2)) * (n : ℂ) ^ ν *
      ((y : ℂ) ^ (om k ν s - 1 - 1) * ((Real.exp (-(4 * π * (n : ℝ) ^ 2 * y)) : ℝ) : ℂ))) (volume.restrict (Ioi 0)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha0]
    · refine Integrable.const_mul ?_ _
      have hr : (0:ℝ) < 4 * π * (n : ℝ) ^ 2 := by positivity
      have hbd : IntegrableOn (fun y : ℝ => y ^ ((om k ν s - 1).re - 1) * Real.exp (-(4 * π * (n : ℝ) ^ 2 * y))) (Ioi 0) :=
        (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (om k ν s - 1).re - 1) (p := 1) (b := 4 * π * (n : ℝ) ^ 2)
          (by linarith) one_pos hr).congr_fun
          (fun y _ => by simp only [Real.rpow_one, neg_mul]) measurableSet_Ioi
      refine Integrable.mono' hbd ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
        refine ContinuousOn.mul ?_ (by fun_prop : Continuous fun y : ℝ =>
          ((Real.exp (-(4 * π * (n : ℝ) ^ 2 * y)) : ℝ) : ℂ)).continuousOn
        exact ContinuousOn.cpow Complex.continuous_ofReal.continuousOn continuousOn_const
          (fun y hy => Complex.ofReal_mem_slitPlane.mpr hy)
      · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
        have hy0 : 0 < y := hy
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le, show (om k ν s - 1 - 1).re = (om k ν s - 1).re - 1 by simp]
  have hFsum : Summable fun n : ℕ => ∫ y in Ioi (0:ℝ), ‖2 * (ψ (n : ZMod M) * a (n ^ 2)) * (n : ℂ) ^ ν *
      ((y : ℂ) ^ (om k ν s - 1 - 1) * ((Real.exp (-(4 * π * (n : ℝ) ^ 2 * y)) : ℝ) : ℂ))‖ := by
    refine ((coeff_summable k M ν ψ a C ha0 han s hs).mul_left (Real.Gamma (om k ν s - 1).re)).congr (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha0]
    · have hr : (0:ℝ) < 4 * π * (n : ℝ) ^ 2 := by positivity
      have hEq : ∫ y in Ioi (0:ℝ), ‖2 * (ψ (n : ZMod M) * a (n ^ 2)) * (n : ℂ) ^ ν *
          ((y : ℂ) ^ (om k ν s - 1 - 1) * ((Real.exp (-(4 * π * (n : ℝ) ^ 2 * y)) : ℝ) : ℂ))‖ =
          ∫ y in Ioi (0:ℝ), ‖2 * (ψ (n : ZMod M) * a (n ^ 2)) * (n : ℂ) ^ ν‖ *
            (y ^ ((om k ν s - 1).re - 1) * Real.exp (-(4 * π * (n : ℝ) ^ 2 * y))) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
        have hy0 : 0 < y := hy
        rw [norm_mul (_ : ℂ) ((y : ℂ) ^ (om k ν s - 1 - 1) * _), norm_mul ((y : ℂ) ^ (om k ν s - 1 - 1)),
          Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le, show (om k ν s - 1 - 1).re = (om k ν s - 1).re - 1 by simp]
      rw [hEq, integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hA hr,
        Real.div_rpow zero_le_one hr.le, Real.one_rpow]
      ring
  rw [← integral_tsum_of_summable_integral_norm hFint hFsum]
  have hterm : ∀ n : ℕ, ∫ y in Ioi (0:ℝ), 2 * (ψ (n : ZMod M) * a (n ^ 2)) * (n : ℂ) ^ ν *
      ((y : ℂ) ^ (om k ν s - 1 - 1) * ((Real.exp (-(4 * π * (n : ℝ) ^ 2 * y)) : ℝ) : ℂ)) =
      2 * Gamma (om k ν s - 1) * (4 * π : ℂ) ^ (1 - om k ν s) *
        LSeries.term (fun n => ψ n * a (n ^ 2)) (s + k - 1) n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha0]
    · have hr : (0:ℝ) < 4 * π * (n : ℝ) ^ 2 := by positivity
      have hI : ∫ y in Ioi (0:ℝ), (y : ℂ) ^ (om k ν s - 1 - 1) * ((Real.exp (-(4 * π * (n : ℝ) ^ 2 * y)) : ℝ) : ℂ) =
          (1 / ((4 * π * (n : ℝ) ^ 2 : ℝ) : ℂ)) ^ (om k ν s - 1) * Gamma (om k ν s - 1) := by
        rw [← Complex.integral_cpow_mul_exp_neg_mul_Ioi hA hr]
        refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
        rw [Complex.ofReal_exp]
        congr 2
        first
          | (push_cast; ring)
          | push_cast
      rw [← coeff_term k M ν ψ a ha0 s n, integral_const_mul, hI, one_div,
        Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_pos.ne)]
      ring
  rw [tsum_congr hterm, tsum_mul_left]
  rfl

end GlobalTheory.CompanionTheory.HalfWt
