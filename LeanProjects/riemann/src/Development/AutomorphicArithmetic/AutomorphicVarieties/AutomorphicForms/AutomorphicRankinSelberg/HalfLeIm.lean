import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open MeasureTheory Set
open UpperHalfPlane hiding I

namespace UpperTheory.V.Af.Rs

private theorem half_le_im {z : ℍ} (hz : z ∈ ModularGroup.fd) : 1 / 2 ≤ z.im := by
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have := z.im_pos
  nlinarith

private theorem norm_G_cls_mul_ker_le_of_mem_fd {L : ℕ} (G : (Fin 2 → ZMod L) → ℍ → ℂ) (C s : ℝ)
    (hC : ∀ (v : Fin 2 → ZMod L) (z : ℍ), 1 / 2 ≤ z.im → ‖G v z‖ * z.im ^ 3 ≤ C)
    (hk : ∀ (x : Fin 2 → ℤ), ∀ z ∈ ModularGroup.fd, ker s x z ≤ 4 * z.im ^ 2 * ‖x‖ ^ (-(2 * s)))
    (h0 : ∀ (x : Fin 2 → ℤ) (z : ℍ), 0 ≤ ker s x z) (x : Fin 2 → ℤ) (z : ℍ)
    (hz : z ∈ ModularGroup.fd) :
    ‖G (cls L x) z * (ker s x z : ℂ)‖ ≤ 8 * C * ‖x‖ ^ (-(2 * s)) := by
  have him := half_le_im hz
  have hw : 0 ≤ ‖x‖ ^ (-(2 * s)) := Real.rpow_nonneg (norm_nonneg _) _
  have hG := hC (cls L x) z him
  have hn : 0 ≤ ‖G (cls L x) z‖ := norm_nonneg _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 x z)]
  have h2 : ‖G (cls L x) z‖ * z.im ^ 2 ≤ 2 * C := by
    nlinarith [mul_nonneg (mul_nonneg hn (sq_nonneg z.im)) (sub_nonneg.2 him)]
  calc ‖G (cls L x) z‖ * ker s x z
      ≤ ‖G (cls L x) z‖ * (4 * z.im ^ 2 * ‖x‖ ^ (-(2 * s))) :=
        mul_le_mul_of_nonneg_left (hk x z hz) hn
    _ = 4 * (‖G (cls L x) z‖ * z.im ^ 2) * ‖x‖ ^ (-(2 * s)) := by ring
    _ ≤ 4 * (2 * C) * ‖x‖ ^ (-(2 * s)) := by gcongr
    _ = 8 * C * ‖x‖ ^ (-(2 * s)) := by ring

private theorem sum_cls (L : ℕ) [NeZero L] (g : (Fin 2 → ZMod L) → ℂ) (s : ℝ) (z : ℍ)
    (hs : Summable fun x => ker s x z) :
    ∑' x : Fin 2 → ℤ, g (cls L x) * (ker s x z : ℂ) = ∑ v, g v * (Zc L v s z : ℂ) := by
  have hc : ∀ v, Summable fun x : Fin 2 → ℤ => if cls L x = v then g v * (ker s x z : ℂ) else 0 := by
    intro v
    have := ((Complex.ofRealCLM.summable hs).mul_left (g v)).indicator {x | cls L x = v}
    refine this.congr (fun x => ?_)
    simp [Set.indicator_apply]
  calc ∑' x : Fin 2 → ℤ, g (cls L x) * (ker s x z : ℂ)
      = ∑' x : Fin 2 → ℤ, ∑ v, if cls L x = v then g v * (ker s x z : ℂ) else 0 := by
        refine tsum_congr (fun x => ?_)
        rw [Finset.sum_ite_eq]
        simp
    _ = ∑ v, ∑' x : Fin 2 → ℤ, if cls L x = v then g v * (ker s x z : ℂ) else 0 :=
        Summable.tsum_finsetSum (fun v _ => hc v)
    _ = ∑ v, g v * (Zc L v s z : ℂ) := by
        refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [Zc, Complex.ofReal_tsum, ← tsum_mul_left]
        refine tsum_congr (fun x => ?_)
        split_ifs <;> simp

end UpperTheory.V.Af.Rs

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.swap :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.Swap := by
  intro hfd hkb hw L _ G hG s hs
  obtain ⟨hGc, C, hC⟩ := hG
  have hs' : s ∈ Icc (1:ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨hkc, hk0, -, -, -, hkb'⟩ := hkb s hs'
  have hsum : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * s)) := hw.1 (2 * s) (by linarith [hs.1])
  have hbd : ∀ x : Fin 2 → ℤ, ∀ z ∈ ModularGroup.fd,
      ‖G (cls L x) z * (ker s x z : ℂ)‖ ≤ 8 * C * ‖x‖ ^ (-(2 * s)) :=
    fun x z hz => norm_G_cls_mul_ker_le_of_mem_fd G C s hC hkb' hk0 x z hz
  have hint : ∀ x : Fin 2 → ℤ,
      IntegrableOn (fun z => G (cls L x) z * (ker s x z : ℂ)) ModularGroup.fd volume := by
    intro x
    exact Measure.integrableOn_of_bounded hfd.2.ne
      ((hGc _).mul (Complex.continuous_ofReal.comp (hkc x))).aestronglyMeasurable
      ((ae_restrict_iff' hfd.1).2 (Filter.Eventually.of_forall (hbd x)))
  refine ⟨hint, ?_⟩
  have hnorm : Summable fun x : Fin 2 → ℤ =>
      ∫ z in ModularGroup.fd, ‖G (cls L x) z * (ker s x z : ℂ)‖ := by
    refine Summable.of_nonneg_of_le (fun x => integral_nonneg (fun _ => norm_nonneg _))
      (fun x => ?_) ((hsum.mul_left (8 * C)).mul_right (volume.real ModularGroup.fd))
    calc ∫ z in ModularGroup.fd, ‖G (cls L x) z * (ker s x z : ℂ)‖
        ≤ ∫ z in ModularGroup.fd, 8 * C * ‖x‖ ^ (-(2 * s)) :=
          setIntegral_mono_on (hint x).norm (integrableOn_const hfd.2.ne) hfd.1 (hbd x)
      _ = 8 * C * ‖x‖ ^ (-(2 * s)) * volume.real ModularGroup.fd := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
  have h := hasSum_integral_of_summable_integral_norm hint hnorm
  have e : TT L G s = ∫ z in ModularGroup.fd, ∑' x : Fin 2 → ℤ, G (cls L x) z * (ker s x z : ℂ) := by
    unfold TT
    refine setIntegral_congr_fun hfd.1 (fun z hz => ?_)
    have hsz : Summable fun x : Fin 2 → ℤ => ker s x z :=
      Summable.of_nonneg_of_le (fun x => hk0 x z) (fun x => hkb' x z hz) (hsum.mul_left _)
    exact (sum_cls L (fun v => G v z) s z hsz).symm
  rw [e]
  exact h
