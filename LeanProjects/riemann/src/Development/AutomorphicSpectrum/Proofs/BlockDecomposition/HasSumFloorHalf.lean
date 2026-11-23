import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

open Ad3 Ad3.S

noncomputable section

namespace GlobalTheory.CompanionTheory.HalfIntZero

variable {M : ℕ} [NeZero M]

theorem hasSum_floorHalf (p : ℕ) (X : ℂ) (hX : ‖(p : ℂ) * X ^ 2‖ < 1) :
    HasSum (fun j : ℕ => ((p ^ (j / 2) : ℕ) : ℂ) * X ^ j) ((1 - p * X ^ 2)⁻¹ + X * (1 - p * X ^ 2)⁻¹) := by
  have hg := hasSum_geometric_of_norm_lt_one hX
  have he : HasSum (fun k : ℕ => ((p ^ ((2 * k) / 2) : ℕ) : ℂ) * X ^ (2 * k)) ((1 - p * X ^ 2)⁻¹) := by
    have : (fun k : ℕ => ((p ^ ((2 * k) / 2) : ℕ) : ℂ) * X ^ (2 * k)) = fun k : ℕ => ((p : ℂ) * X ^ 2) ^ k := by
      funext k
      rw [Nat.mul_div_cancel_left k (by norm_num : 0 < 2), mul_pow, pow_mul]
      push_cast
      rfl
    rw [this]
    exact hg
  have ho : HasSum (fun k : ℕ => ((p ^ ((2 * k + 1) / 2) : ℕ) : ℂ) * X ^ (2 * k + 1)) (X * (1 - p * X ^ 2)⁻¹) := by
    have : (fun k : ℕ => ((p ^ ((2 * k + 1) / 2) : ℕ) : ℂ) * X ^ (2 * k + 1)) = fun k : ℕ => X * ((p : ℂ) * X ^ 2) ^ k := by
      funext k
      have h : (2 * k + 1) / 2 = k := by omega
      rw [h, mul_pow, pow_succ, pow_mul]
      push_cast
      ring
    rw [this]
    exact hg.mul_left X
  exact HasSum.even_add_odd he ho

omit [NeZero M] in

theorem sq_char_cpow (c : DirichletCharacter ℂ M) (p : ℕ) (hp : p ≠ 0) (s : ℂ) :
    (c ^ 2) (p : ZMod M) * (p : ℂ) ^ (-(2 * s - 1)) = p * (c (p : ZMod M) * (p : ℂ) ^ (-s)) ^ 2 := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp
  have h1 : (p : ℂ) ^ (-(2 * s - 1)) = p * ((p : ℂ) ^ (-s)) ^ 2 := by
    rw [show -(2 * s - 1) = 1 + (-s + -s) by ring, Complex.cpow_add _ _ hp0, Complex.cpow_add _ _ hp0,
      Complex.cpow_one]
    ring
  rw [h1, MulChar.pow_apply' c (by norm_num : 2 ≠ 0)]
  ring

theorem local_factor (hN : N2) (h2 : 2 ∣ M) (c : DirichletCharacter ℂ M) (s : ℂ) (hs : 1 < s.re)
    (p : Nat.Primes) :
    (∑' j : ℕ, (NN 0 ((p : ℕ) ^ j) : ℂ) * (c ((p : ℕ) : ZMod M) * ((p : ℕ) : ℂ) ^ (-s)) ^ j) /
        (1 + c ((p : ℕ) : ZMod M) * ((p : ℕ) : ℂ) ^ (-s)) =
      (1 - (c ^ 2) ((p : ℕ) : ZMod M) * ((p : ℕ) : ℂ) ^ (-(2 * s - 1)))⁻¹ := by
  have hpp : (p : ℕ).Prime := p.2
  rw [sq_char_cpow c p hpp.ne_zero s]
  by_cases hc : c ((p : ℕ) : ZMod M) = 0
  · rw [hc]
    have h0 : (∑' j : ℕ, (NN 0 ((p : ℕ) ^ j) : ℂ) * ((0 : ℂ) * ((p : ℕ) : ℂ) ^ (-s)) ^ j) = 1 := by
      rw [tsum_eq_single 0]
      · simp [(hN 0).1]
      · intro j hj
        simp [hj]
    rw [h0]
    simp
  · have hne : (p : ℕ) ≠ 2 := by
      intro h
      apply hc
      rw [h]
      apply MulChar.map_nonunit
      intro hu
      have hu' : IsUnit (((2 : ℕ)) : ZMod M) := by exact_mod_cast hu
      have := (ZMod.isUnit_iff_coprime 2 M).1 hu'
      exact absurd (Nat.Coprime.eq_one_of_dvd this h2) (by norm_num)
    set X : ℂ := c ((p : ℕ) : ZMod M) * ((p : ℕ) : ℂ) ^ (-s) with hXdef
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
    have hXle : ‖X‖ ≤ ((p : ℕ) : ℝ)⁻¹ := by
      rw [hXdef, norm_mul, Complex.norm_natCast_cpow_of_pos hpp.pos]
      have h1 : ‖c ((p : ℕ) : ZMod M)‖ ≤ 1 := DirichletCharacter.norm_le_one c _
      have h2' : ((p : ℕ) : ℝ) ^ (-s).re ≤ ((p : ℕ) : ℝ)⁻¹ := by
        rw [← Real.rpow_neg_one]
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        simp only [Complex.neg_re]
        linarith
      calc _ ≤ 1 * ((p : ℕ) : ℝ)⁻¹ :=
            mul_le_mul h1 h2' (Real.rpow_nonneg hp0.le _) zero_le_one
        _ = _ := one_mul _
    have hinv : ((p : ℕ) : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hp2
    have hnX : ‖(((p : ℕ) : ℂ)) * X ^ 2‖ < 1 := by
      rw [norm_mul, norm_pow, Complex.norm_natCast]
      have hsq : ‖X‖ ^ 2 ≤ (((p : ℕ) : ℝ)⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hXle 2
      calc ((p : ℕ) : ℝ) * ‖X‖ ^ 2 ≤ ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)⁻¹) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq hp0.le
        _ = ((p : ℕ) : ℝ)⁻¹ := by field_simp
        _ < 1 := by linarith
    have h1X : 1 + X ≠ 0 := by
      intro h
      have : X = -1 := by linear_combination h
      rw [this] at hXle
      simp only [norm_neg, norm_one] at hXle
      linarith
    have h1pX : 1 - ((p : ℕ) : ℂ) * X ^ 2 ≠ 0 := by
      intro h
      have : ((p : ℕ) : ℂ) * X ^ 2 = 1 := by linear_combination -h
      rw [this] at hnX
      simp at hnX
    have hterm : (fun j : ℕ => (NN 0 ((p : ℕ) ^ j) : ℂ) * X ^ j) =
        fun j : ℕ => (((p : ℕ) ^ (j / 2) : ℕ) : ℂ) * X ^ j := by
      funext j
      rw [(((hN 0).2.2.2 p j hpp hne).2.2 rfl)]
    rw [hterm, (hasSum_floorHalf p X hnX).tsum_eq]
    field_simp

theorem coeff_zero (hN : N2) (hA : A2) (h2 : 2 ∣ M) (c : DirichletCharacter ℂ M) (s : ℂ) (hs : 2 < s.re) :
    DirichletCharacter.LFunction (c ^ 2) (2 * s) * Dn c 0 s =
      LSeries (fun n : ℕ => (c ^ 2) (n : ZMod M)) (2 * s - 1) := by
  have hr : 1 < (2 * s - 1).re := by
    simp
    linarith
  have e1 := (hA M c 0 s hs).2
  have e2 := DirichletCharacter.LSeries_eulerProduct_hasProd (c ^ 2) hr
  have e3 : (fun p : Nat.Primes => (∑' j : ℕ, (NN 0 ((p : ℕ) ^ j) : ℂ) * (c ((p : ℕ) : ZMod M) * ((p : ℕ) : ℂ) ^ (-s)) ^ j) /
        (1 + c ((p : ℕ) : ZMod M) * ((p : ℕ) : ℂ) ^ (-s))) =
      fun p : Nat.Primes => (1 - (c ^ 2) ((p : ℕ) : ZMod M) * ((p : ℕ) : ℂ) ^ (-(2 * s - 1)))⁻¹ := by
    funext p
    exact local_factor hN h2 c s (by linarith) p
  rw [e3] at e1
  exact e1.unique e2

theorem cont_zero (h2 : 2 ∣ M) (c : DirichletCharacter ℂ M) (G : ℂ → ℂ)
    (hG : DifferentiableOn ℂ G (HP (-1)))
    (hGs : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * LSeries (fun n : ℕ => (c ^ 2) (n : ZMod M)) s) :
    G 0 = 0 := by
  have hlin : IsLinearMap ℝ (fun u : ℂ => u.re - u.im) :=
    ⟨fun x y => by simp only [Complex.add_re, Complex.add_im]; ring,
      fun a x => by simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, smul_eq_mul]; ring⟩
  let U : Set ℂ := {u | -1 < u.re} ∩ {u | u.re - u.im < 1}
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (Complex.continuous_re.sub Complex.continuous_im) continuous_const)
  have hUc : Convex ℝ U := (convex_halfSpace_re_gt (-1)).inter (convex_halfSpace_lt hlin 1)
  have hF : DifferentiableOn ℂ (fun u : ℂ => (u - 1) * DirichletCharacter.LFunction (c ^ 2) u) U := by
    intro u hu
    have hu1 : u ≠ 1 := by
      rintro rfl
      have := hu.2
      simp at this
    exact ((differentiableAt_id.sub_const 1).mul
      (DirichletCharacter.differentiableAt_LFunction _ u (Or.inl hu1))).differentiableWithinAt
  have hGU : DifferentiableOn ℂ G U := hG.mono (fun u hu => hu.1)
  have hz : (⟨2, 2⟩ : ℂ) ∈ U := by
    constructor
    · show (-1 : ℝ) < 2
      norm_num
    · show (2 : ℝ) - 2 < 1
      norm_num
  have hev : G =ᶠ[nhds (⟨2, 2⟩ : ℂ)] fun u : ℂ => (u - 1) * DirichletCharacter.LFunction (c ^ 2) u := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (⟨2, 2⟩ : ℂ).re by norm_num)] with z hz
    rw [hGs z hz, DirichletCharacter.LFunction_eq_LSeries _ hz]
  have key := (hGU.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hF.analyticOnNhd hUo)
    hUc.isPreconnected hz hev
  have h0U : (0 : ℂ) ∈ U := by
    constructor
    · show (-1 : ℝ) < (0 : ℂ).re
      simp
    · show (0 : ℂ).re - (0 : ℂ).im < 1
      simp
  have hM : 1 < M := by
    have := Nat.le_of_dvd (NeZero.pos M) h2
    omega
  haveI : Fact (1 < M) := ⟨hM⟩
  have hev' : Function.Even (c ^ 2 : DirichletCharacter ℂ M) := by
    intro x
    have hm : c (-1) ^ 2 = 1 := by
      rw [← map_pow]
      simp
    rw [MulChar.pow_apply' c (by norm_num : 2 ≠ 0), MulChar.pow_apply' c (by norm_num : 2 ≠ 0),
      neg_eq_neg_one_mul x, map_mul, mul_pow, hm, one_mul]
  have hL : DirichletCharacter.LFunction (c ^ 2) 0 = 0 := by
    rw [DirichletCharacter.LFunction, ZMod.LFunction_apply_zero_of_even hev',
      MulChar.map_nonunit _ not_isUnit_zero]
    simp
  have := key h0U
  simpa [hL] using this

theorem main : LB → N2 → A2 → A0 := by
  rintro ⟨C₀, hLB⟩ hN hA M _ h2 c
  obtain ⟨G, hGd, hGs, hGb⟩ := hLB M (fun n : ℕ => (c ^ 2) (n : ZMod M)) (NeZero.pos M)
    (fun n => by simp) (fun n => DirichletCharacter.norm_le_one _ _)
  have hG0 := cont_zero h2 c G hGd hGs
  let g : ℂ → ℂ := fun s => G (2 * s - 1) / 2
  have hgd : DifferentiableOn ℂ g (HP (1 / 4)) := by
    have hmaps : Set.MapsTo (fun s : ℂ => 2 * s - 1) (HP (1 / 4)) (HP (-1)) := by
      intro s hs
      have hs' : (1 / 4 : ℝ) < s.re := hs
      show (-1 : ℝ) < (2 * s - 1).re
      simp
      linarith
    have hlin : DifferentiableOn ℂ (fun s : ℂ => 2 * s - 1) (HP (1 / 4)) := by fun_prop
    exact (hGd.comp hlin hmaps).div_const 2
  have hopen : IsOpen (HP (1 / 4)) := isOpen_lt continuous_const Complex.continuous_re
  have hhalf : (1 / 2 : ℂ) ∈ HP (1 / 4) := by
    show (1 / 4 : ℝ) < (1 / 2 : ℂ).re
    norm_num
  have hAd : DifferentiableOn ℂ (dslope g (1 / 2)) (HP (1 / 4)) :=
    (Complex.differentiableOn_dslope (hopen.mem_nhds hhalf)).2 hgd
  have hball : Metric.closedBall (1 / 2 : ℂ) (1 / 5) ⊆ HP (1 / 4) := by
    intro s hs
    have h1 : ‖s - 1 / 2‖ ≤ 1 / 5 := by simpa [dist_eq_norm] using hs
    have h2' := (abs_le.1 ((Complex.abs_re_le_norm (s - 1 / 2)).trans h1)).1
    show (1 / 4 : ℝ) < s.re
    simp at h2'
    norm_num at h2'
    linarith
  obtain ⟨K, hK⟩ := (isCompact_closedBall (1 / 2 : ℂ) (1 / 5)).exists_bound_of_continuousOn
    (hAd.continuousOn.mono hball)
  have hg2 : g (1 / 2) = 0 := by
    show G (2 * (1 / 2) - 1) / 2 = 0
    norm_num [hG0]
  refine ⟨max K 0 + 40 * |C₀| * (M : ℝ) ^ 2, dslope g (1 / 2), hAd, ?_, ?_⟩
  · intro s hs
    have h := sub_smul_dslope g (1 / 2) s
    rw [smul_eq_mul, hg2, sub_zero] at h
    rw [h, mul_assoc, coeff_zero hN hA h2 c s hs]
    show G (2 * s - 1) / 2 = _
    rw [hGs (2 * s - 1) (by simp; linarith)]
    ring
  · intro s hs
    have hone : (1 : ℝ) ≤ (1 + ‖s‖) ^ 4 := one_le_pow₀ (by linarith [norm_nonneg s])
    have hCnn : 0 ≤ 40 * |C₀| * (M : ℝ) ^ 2 := by positivity
    have hpos : 0 ≤ (1 + ‖s‖) ^ 4 := by positivity
    by_cases hb : ‖s - 1 / 2‖ ≤ 1 / 5
    · have h1 : ‖dslope g (1 / 2) s‖ ≤ K := hK s (by simpa [dist_eq_norm] using hb)
      have h2' : K ≤ max K 0 := le_max_left _ _
      have h3 : 0 ≤ max K 0 := le_max_right _ _
      nlinarith
    · push_neg at hb
      have hne : s ≠ 1 / 2 := by
        rintro rfl
        simp at hb
        norm_num at hb
      have hnn : 0 < ‖s - 1 / 2‖ := by linarith
      rw [dslope_of_ne _ hne, slope_def_field, hg2, sub_zero, norm_div]
      have hre : -1 / 2 ≤ (2 * s - 1).re := by
        have hs' : (1 / 4 : ℝ) < s.re := hs
        simp
        linarith
      have hG := hGb (2 * s - 1) hre
      have hnorm : 1 + ‖2 * s - 1‖ ≤ 2 * (1 + ‖s‖) := by
        have : ‖2 * s - 1‖ ≤ 2 * ‖s‖ + 1 := by
          refine (norm_sub_le _ _).trans ?_
          simp
        linarith
      have hpow : (1 + ‖2 * s - 1‖) ^ 4 ≤ 16 * (1 + ‖s‖) ^ 4 := by
        have := pow_le_pow_left₀ (by positivity) hnorm 4
        calc _ ≤ (2 * (1 + ‖s‖)) ^ 4 := this
          _ = _ := by ring
      have hGn : ‖G (2 * s - 1)‖ ≤ |C₀| * (M : ℝ) ^ 2 * (16 * (1 + ‖s‖) ^ 4) := by
        refine hG.trans ?_
        have hq : 0 ≤ (M : ℝ) ^ 2 := by positivity
        have hp1 : 0 ≤ (1 + ‖2 * s - 1‖) ^ 4 := by positivity
        calc C₀ * (M : ℝ) ^ 2 * (1 + ‖2 * s - 1‖) ^ 4
            ≤ |C₀| * (M : ℝ) ^ 2 * (1 + ‖2 * s - 1‖) ^ 4 := by
              gcongr
              exact le_abs_self _
          _ ≤ _ := by gcongr
      have hgs : ‖g s‖ = ‖G (2 * s - 1)‖ / 2 := by
        show ‖G (2 * s - 1) / 2‖ = _
        simp
      rw [hgs, div_le_iff₀ hnn]
      have h3 : 0 ≤ max K 0 := le_max_right _ _
      have hb' : (1 / 5 : ℝ) ≤ ‖s - 1 / 2‖ := hb.le
      have hbase : 0 ≤ 40 * |C₀| * (M : ℝ) ^ 2 * (1 + ‖s‖) ^ 4 := by positivity
      have hX : ‖G (2 * s - 1)‖ / 2 ≤ (40 * |C₀| * (M : ℝ) ^ 2 * (1 + ‖s‖) ^ 4) * (1 / 5) := by
        nlinarith
      calc ‖G (2 * s - 1)‖ / 2 ≤ (40 * |C₀| * (M : ℝ) ^ 2 * (1 + ‖s‖) ^ 4) * (1 / 5) := hX
        _ ≤ (40 * |C₀| * (M : ℝ) ^ 2 * (1 + ‖s‖) ^ 4) * ‖s - 1 / 2‖ := by gcongr
        _ ≤ _ := by
          have : 0 ≤ max K 0 * (1 + ‖s‖) ^ 4 * ‖s - 1 / 2‖ := by positivity
          nlinarith

end GlobalTheory.CompanionTheory.HalfIntZero

end
