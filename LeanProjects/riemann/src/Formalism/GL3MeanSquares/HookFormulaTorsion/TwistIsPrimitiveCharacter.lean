import Mathlib
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis

open DirichletCharacter

namespace Formalism.HermitianLattices.ThinSetIntegral

private lemma qc_ne_one (q : ℕ) [Fact q.Prime] (h2 : q ≠ 2) : Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q ≠ 1 := by
  intro h
  apply quadraticChar_ne_one (F := ZMod q) (by rwa [ZMod.ringChar_zmod_n])
  refine MulChar.ext fun a => ?_
  have h1 := congrArg (fun χ : DirichletCharacter ℂ q => χ (a : ZMod q)) h
  simp only [Formalism.HermitianLattices.ZeroFreeRegionGL2.qc, MulChar.ringHomComp_apply, Int.coe_castRingHom,
    MulChar.one_apply_coe] at h1
  rw [MulChar.one_apply_coe]
  exact_mod_cast h1

private lemma qc_prim (q : ℕ) [Fact q.Prime] (h2 : q ≠ 2) : (Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q).IsPrimitive := by
  have hd := conductor_dvd_level (Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q)
  rcases (Nat.dvd_prime (Fact.out : q.Prime)).1 hd with h | h
  · exact absurd (eq_one_iff_conductor_eq_one.2 h) (qc_ne_one q h2)
  · exact h

private lemma qc_sq (q : ℕ) [Fact q.Prime] : Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q ^ 2 = 1 := by
  refine MulChar.ext fun a => ?_
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  simp only [Formalism.HermitianLattices.ZeroFreeRegionGL2.qc, MulChar.ringHomComp_apply, Int.coe_castRingHom]
  rw [← Int.cast_pow, quadraticChar_sq_one a.ne_zero, Int.cast_one]

private lemma prim_mul {N m n : ℕ} [NeZero N] (hm : m ∣ N) (hn : n ∣ N) (hco : m.Coprime n) (hN : N = m * n)
    (χ₁ : DirichletCharacter ℂ m) (χ₂ : DirichletCharacter ℂ n) (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    (changeLevel hm χ₁ * changeLevel hn χ₂).IsPrimitive := by
  have cA : (changeLevel hm χ₁).conductor = m := by rw [conductor_changeLevel]; exact h1
  have cB : (changeLevel hn χ₂).conductor = n := by rw [conductor_changeLevel]; exact h2
  generalize changeLevel hm χ₁ = A at *
  generalize changeLevel hn χ₂ = B at *
  have d1 : m ∣ (A * B).conductor.lcm n := by
    have h := conductor_mul_dvd_lcm_conductor (A * B) B⁻¹
    rwa [mul_inv_cancel_right, conductor_inv, cA, cB] at h
  have d2 : n ∣ (A * B).conductor.lcm m := by
    have h := conductor_mul_dvd_lcm_conductor (B * A) A⁻¹
    rwa [mul_inv_cancel_right, conductor_inv, cA, cB, mul_comm B A] at h
  have e1 : m ∣ (A * B).conductor :=
    hco.dvd_of_dvd_mul_right (d1.trans (Nat.lcm_dvd_mul _ _))
  have e2 : n ∣ (A * B).conductor :=
    hco.symm.dvd_of_dvd_mul_right (d2.trans (Nat.lcm_dvd_mul _ _))
  rw [isPrimitive_def]
  have e3 : N ∣ (A * B).conductor := by
    have h := hco.mul_dvd_of_dvd_of_dvd e1 e2
    rwa [← hN] at h
  exact Nat.dvd_antisymm (conductor_dvd_level _) e3

private lemma chi_eight_sq : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8 ^ 2 = 1 := by
  refine MulChar.ext fun a => ?_
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  simp only [Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8, MulChar.ringHomComp_apply, Int.coe_castRingHom]
  have hu : IsUnit (ZMod.χ₈ (a : ZMod 8)) := by
    rw [← MulChar.coe_toUnitHom]
    exact Units.isUnit _
  rcases ZMod.isQuadratic_χ₈ (a : ZMod 8) with h | h | h
  · rw [h] at hu
    exact absurd hu not_isUnit_zero
  · rw [h]
    norm_num
  · rw [h]
    norm_num

private lemma chi_eight_primitive : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.IsPrimitive := by
  rw [isPrimitive_def]
  by_contra hne
  have hd := conductor_dvd_level Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8
  have h4 : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.conductor ∣ 4 := by
    have hle : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.conductor ≤ 8 := Nat.le_of_dvd (by norm_num) hd
    generalize Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.conductor = k at *
    interval_cases k <;> omega
  obtain ⟨hd4, χ₀, h0⟩ : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.FactorsThrough 4 :=
    (mem_conductorSet_iff_conductor_dvd _ (by norm_num)).2 h4
  have h5 : changeLevel hd4 χ₀ ((5 : ℤ) : ZMod 8) = χ₀ ((5 : ℤ) : ZMod 4) :=
    changeLevel_eq_cast_of_dvd' χ₀ hd4 (by
      rw [Int.isCoprime_iff_gcd_eq_one]; decide)
  rw [← h0] at h5
  have h6 : ((5 : ℤ) : ZMod 4) = 1 := by decide
  have h7 : ZMod.χ₈ ((5 : ℤ) : ZMod 8) = -1 := by decide
  rw [h6, map_one, Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8, MulChar.ringHomComp_apply, h7] at h5
  norm_num at h5

theorem twist_is_primitive_character : Formalism.HermitianLattices.ZeroFreeRegionGL2.TwPrimitive := by
  refine ⟨⟨chi_eight_primitive, chi_eight_sq⟩, ?_⟩
  intro t θ q _ hθ h2 hco
  have hq : q.Prime := Fact.out
  have ht : t ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_right] at hco
    exact hq.one_lt.ne' hco
  have : NeZero t := ⟨ht⟩
  have hp : (Formalism.HermitianLattices.ZeroFreeRegionGL2.tw θ q).IsPrimitive :=
    prim_mul _ _ hco.symm rfl θ (Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q) hθ (qc_prim q h2)
  refine ⟨hp, ?_, ?_⟩
  · intro h1
    rw [isPrimitive_def, h1, conductor_one] at hp
    have h3 : 2 ≤ q := hq.two_le
    have h4 : 1 ≤ t := Nat.pos_of_ne_zero ht
    nlinarith
  · intro hs
    rw [Formalism.HermitianLattices.ZeroFreeRegionGL2.tw, mul_pow, ← map_pow, ← map_pow, hs, qc_sq, map_one, map_one, one_mul]

private lemma K_int (b : ℝ) (hb : 0 < b) :
    MeasureTheory.IntegrableOn (fun v : ℝ => v ^ (2 : ℝ) * Real.exp (-b * v ^ (3 / 8 : ℝ))) (Set.Ioi 0) := by
  exact integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hb

private lemma ptwise (c lam V v : ℝ) (hc : 0 < c) (hV : 1 ≤ V) (hl1 : 1 ≤ lam) (hl : lam ≤ V ^ (5 / 8 : ℝ))
    (hv : V < v) :
    (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) ≤
      4 * Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) * (v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (3 / 8 : ℝ))) := by
  have hv1 : 1 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hV58 : V ^ (5 / 8 : ℝ) ≤ V := by
    have h := Real.rpow_le_rpow_of_exponent_le hV (show (5 / 8 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have hlv : lam ≤ v := by linarith
  have h58 : lam ≤ v ^ (5 / 8 : ℝ) :=
    le_trans hl (Real.rpow_le_rpow (by linarith) hv.le (by norm_num))
  have hsq : Real.sqrt v ≤ v ^ (5 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
  have hv58 : 0 < v ^ (5 / 8 : ℝ) := by positivity
  have hden : lam + Real.sqrt v ≤ 2 * v ^ (5 / 8 : ℝ) := by linarith
  have hdpos : 0 < lam + Real.sqrt v := by positivity
  have h38 : v ^ (3 / 8 : ℝ) = v / v ^ (5 / 8 : ℝ) := by
    rw [show (3 / 8 : ℝ) = 1 - 5 / 8 by norm_num, Real.rpow_sub hv0, Real.rpow_one]
  have h1 : c / 2 * v ^ (3 / 8 : ℝ) ≤ c * v / (lam + Real.sqrt v) := by
    rw [h38]
    calc c / 2 * (v / v ^ (5 / 8 : ℝ)) = c * v / (2 * v ^ (5 / 8 : ℝ)) := by
          field_simp
      _ ≤ c * v / (lam + Real.sqrt v) :=
          div_le_div_of_nonneg_left (by positivity) hdpos hden
  have h2 : V ^ (3 / 8 : ℝ) ≤ v ^ (3 / 8 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hv.le (by norm_num)
  have hexp : Real.exp (-c * v / (lam + Real.sqrt v)) ≤
      Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) * Real.exp (-(c / 4) * v ^ (3 / 8 : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h3 : -c * v / (lam + Real.sqrt v) = -(c * v / (lam + Real.sqrt v)) := by ring
    rw [h3]
    nlinarith
  have hpoly : (v + lam) ^ 2 ≤ 4 * v ^ (2 : ℝ) := by
    rw [show (v ^ (2 : ℝ)) = v ^ 2 by norm_cast]
    nlinarith
  calc (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))
      ≤ (4 * v ^ (2 : ℝ)) * (Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) * Real.exp (-(c / 4) * v ^ (3 / 8 : ℝ))) :=
        mul_le_mul hpoly hexp (by positivity) (by positivity)
    _ = 4 * Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) * (v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (3 / 8 : ℝ))) := by
        ring

private lemma half_rpow (y a : ℝ) (hy : 0 ≤ y) (ha1 : a ≤ 1) : y ^ a / 2 ≤ (y / 2) ^ a := by
  rw [Real.div_rpow hy (by norm_num)]
  have h2 : (2 : ℝ) ^ a ≤ 2 := by
    calc (2 : ℝ) ^ a ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ha1
      _ = 2 := Real.rpow_one 2
  have hpos : 0 < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy a) hpos h2

theorem thin_set_integral : Formalism.HermitianLattices.ZeroFreeRegionGL2.ThinIntegral := by
  intro ε c hε hc
  have hb : 0 < c / 4 := by positivity
  have hKi := K_int (c / 4) hb
  set g : ℝ → ℝ := fun v : ℝ => v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (3 / 8 : ℝ)) with hg
  set K := ∫ v in Set.Ioi (0 : ℝ), g v with hK
  have E1 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x := Filter.eventually_ge_atTop 1
  have E3 : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ x ^ (ε / 3) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop 2
  have E2a : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x‖ ≤ 1 * ‖x ^ (ε / 480)‖ :=
    (isLittleO_log_rpow_atTop (show 0 < ε / 480 by positivity)).bound one_pos
  have E2b : ∀ᶠ x : ℝ in Filter.atTop, 4 ≤ x ^ (ε / 240) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop 4
  have E4 : ∀ᶠ x : ℝ in Filter.atTop, 4 * K ≤ Real.exp (c / 16 * x ^ (ε / 8)) :=
    (Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (show 0 < ε / 8 by positivity)).const_mul_atTop
      (show 0 < c / 16 by positivity))).eventually_ge_atTop (4 * K)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 (E1.and (E3.and (E2a.and (E2b.and E4))))
  refine ⟨c / 16, x₀, by positivity, ?_⟩
  intro x hx V lam hV hl1 hl
  obtain ⟨h1, h3, h2a, h2b, h4⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have hV1 : 1 ≤ V := by linarith
  have hV0 : 0 ≤ x ^ (ε / 3) / 2 := by positivity

  have hlV : lam ≤ V ^ (5 / 8 : ℝ) := by
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg h1
    have hr0 : 0 < x ^ (ε / 480) := Real.rpow_pos_of_pos hx0 _
    have hlog : Real.log x ≤ x ^ (ε / 480) := by
      rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hr0.le, one_mul] at h2a
      exact h2a
    have hlog2 : Real.log x ^ 2 ≤ x ^ (ε / 240) := by
      have e : x ^ (ε / 240) = (x ^ (ε / 480)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
      rw [e]
      gcongr
    have e5 : (x ^ (ε / 3)) ^ (5 / 8 : ℝ) = x ^ (ε / 5) * x ^ (ε / 240) * x ^ (ε / 240) := by
      rw [← Real.rpow_mul hx0.le, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
    have hh := half_rpow (x ^ (ε / 3)) (5 / 8) (by positivity) (by norm_num)
    have hm : (x ^ (ε / 3) / 2) ^ (5 / 8 : ℝ) ≤ V ^ (5 / 8 : ℝ) := Real.rpow_le_rpow hV0 hV (by norm_num)
    have ha : 0 < x ^ (ε / 5) := Real.rpow_pos_of_pos hx0 _
    have hb' : 0 < x ^ (ε / 240) := Real.rpow_pos_of_pos hx0 _
    have s1 : 2 * x ^ (ε / 5) * Real.log x ^ 2 ≤ 2 * x ^ (ε / 5) * x ^ (ε / 240) := by gcongr
    have s2 : 2 * x ^ (ε / 5) * x ^ (ε / 240) * 4 ≤ 2 * x ^ (ε / 5) * x ^ (ε / 240) * x ^ (ε / 240) := by gcongr
    rw [e5] at hh
    linarith

  have hW : x ^ (ε / 8) / 2 ≤ V ^ (3 / 8 : ℝ) := by
    have e3 : (x ^ (ε / 3)) ^ (3 / 8 : ℝ) = x ^ (ε / 8) := by
      rw [← Real.rpow_mul hx0.le]; congr 1; ring
    have hh := half_rpow (x ^ (ε / 3)) (3 / 8) (by positivity) (by norm_num)
    have hm : (x ^ (ε / 3) / 2) ^ (3 / 8 : ℝ) ≤ V ^ (3 / 8 : ℝ) := Real.rpow_le_rpow hV0 hV (by norm_num)
    rw [e3] at hh
    linarith
  set A : ℝ := 4 * Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) with hA
  have hA0 : 0 ≤ A := by positivity
  have hpt : ∀ v ∈ Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) ≤ A * g v :=
    fun v hv => ptwise c lam V v hc hV1 hl1 hlV hv
  have hgV : MeasureTheory.IntegrableOn (fun v => A * g v) (Set.Ioi V) :=
    (hKi.mono_set (Set.Ioi_subset_Ioi (by linarith))).const_mul A
  have hcont : Continuous (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) := by
    have hne : ∀ v : ℝ, lam + Real.sqrt v ≠ 0 := fun v => by
      have := Real.sqrt_nonneg v
      linarith
    fun_prop (disch := exact hne _)
  have hfi : MeasureTheory.IntegrableOn
      (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) (Set.Ioi V) := by
    refine MeasureTheory.Integrable.mono' hgV hcont.aestronglyMeasurable ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun v hv => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt v hv
  refine ⟨hfi, ?_⟩
  have hg0 : ∀ v ∈ Set.Ioi (0 : ℝ), 0 ≤ g v := fun v hv => by
    have : (0 : ℝ) < v := hv
    simp only [hg]
    positivity
  have hK0 : 0 ≤ K := MeasureTheory.setIntegral_nonneg measurableSet_Ioi hg0
  have i1 : (∫ v in Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) ≤
      ∫ v in Set.Ioi V, A * g v := MeasureTheory.setIntegral_mono_on hfi hgV measurableSet_Ioi hpt
  have i2 : (∫ v in Set.Ioi V, A * g v) = A * ∫ v in Set.Ioi V, g v := MeasureTheory.integral_const_mul _ _
  have i3 : (∫ v in Set.Ioi V, g v) ≤ K :=
    MeasureTheory.setIntegral_mono_set hKi
      ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hg0))
      (Set.Ioi_subset_Ioi (by linarith : (0 : ℝ) ≤ V)).eventuallyLE
  have i4 : A * K ≤ Real.exp (-(c / 16) * x ^ (ε / 8)) := by
    have j1 : Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) ≤
        Real.exp (-(c / 16) * x ^ (ε / 8)) * Real.exp (-(c / 16 * x ^ (ε / 8))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith
    have j2 : 4 * K * Real.exp (-(c / 16 * x ^ (ε / 8))) ≤ 1 := by
      rw [Real.exp_neg]
      have := Real.exp_pos (c / 16 * x ^ (ε / 8))
      rw [← div_eq_mul_inv, div_le_one this]
      exact h4
    have j3 := Real.exp_pos (-(c / 16) * x ^ (ε / 8))
    calc A * K = 4 * K * Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) := by rw [hA]; ring
      _ ≤ 4 * K * (Real.exp (-(c / 16) * x ^ (ε / 8)) * Real.exp (-(c / 16 * x ^ (ε / 8)))) := by gcongr
      _ = Real.exp (-(c / 16) * x ^ (ε / 8)) * (4 * K * Real.exp (-(c / 16 * x ^ (ε / 8)))) := by ring
      _ ≤ Real.exp (-(c / 16) * x ^ (ε / 8)) * 1 := by gcongr
      _ = _ := mul_one _
  calc _ ≤ A * ∫ v in Set.Ioi V, g v := by rw [← i2]; exact i1
    _ ≤ A * K := by gcongr
    _ ≤ _ := i4

end Formalism.HermitianLattices.ThinSetIntegral
