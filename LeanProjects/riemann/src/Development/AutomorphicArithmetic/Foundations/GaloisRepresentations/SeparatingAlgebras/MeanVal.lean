import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private lemma circle_mean (g : ℂ → ℂ)
    (hd : ∀ u ∈ Metric.closedBall (0 : ℂ) 1, DifferentiableAt ℂ g u) :
    ∫ s : UnitAddCircle, g ((AddCircle.toCircle s : Circle) : ℂ) = g 0 := by
  have hc : ContinuousOn g (Metric.closedBall (0 : ℂ) |1|) := by
    intro u hu
    exact (hd u (by simpa using hu)).continuousAt.continuousWithinAt
  have hmv : Real.circleAverage g 0 1 = g 0 :=
    circleAverage_of_differentiable_on_off_countable (s := ∅) Set.countable_empty hc
      (fun u hu => hd u (by
        have := hu.1
        simp only [abs_one, Metric.mem_ball] at this
        simpa using this.le))
  have hpi : (2 * Real.pi) ≠ 0 := Real.two_pi_pos.ne'
  have e : ∀ a : ℝ, ((AddCircle.toCircle (a : UnitAddCircle) : Circle) : ℂ)
      = circleMap 0 1 (2 * Real.pi * a) := by
    intro a
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp, circleMap]
    simp only [zero_add, Complex.ofReal_one, one_mul]
    congr 1
    push_cast
    ring
  rw [← UnitAddCircle.intervalIntegral_preimage 0, ← hmv, Real.circleAverage_def]
  simp_rw [e]
  rw [intervalIntegral.integral_comp_mul_left (fun θ => g (circleMap 0 1 θ)) hpi]
  simp

private lemma ratio_eq (u : ℂ) (hu : u ≠ 0) (c : ℤ) (i j : ℕ) (hij : i < j) (a b : ℂ) :
    (u ^ (c - (i : ℤ)) * a) / (u ^ (c - (j : ℤ)) * b) = u ^ (j - i) * (a / b) := by
  have h : u ^ (c - (i : ℤ)) / u ^ (c - (j : ℤ)) = u ^ (j - i) := by
    rw [← zpow_sub₀ hu, ← zpow_natCast, Nat.cast_sub hij.le]
    congr 1
    ring
  rw [mul_div_mul_comm, h]

theorem UpperTheory.Gal.Gen.meanVal_pf :
    UpperTheory.Gal.Gen.MeanVal := by
  intro n t ht0 ht1 z hz c m
  set g : ℂ → ℂ := fun u => u ^ m * ∏ p ∈ prs n,
    (1 - u ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ))) /
      (1 - (t : ℂ) * (u ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ)))) with hg
  have hden : ∀ u ∈ Metric.closedBall (0 : ℂ) 1, ∀ p : Fin n × Fin n,
      1 - (t : ℂ) * (u ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ))) ≠ 0 := by
    intro u hu p h0
    have hu1 : ‖u‖ ≤ 1 := by simpa using hu
    have hx : (t : ℂ) * (u ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ))) = 1 :=
      (sub_eq_zero.mp h0).symm
    have hn := congrArg norm hx
    rw [norm_mul, norm_mul, norm_div, hz, hz, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0,
      norm_one, div_one, mul_one] at hn
    have : ‖u‖ ^ ((p.2 : ℕ) - (p.1 : ℕ)) ≤ 1 := pow_le_one₀ (norm_nonneg _) hu1
    nlinarith
  have hd : ∀ u ∈ Metric.closedBall (0 : ℂ) 1, DifferentiableAt ℂ g u := by
    intro u hu
    refine (differentiableAt_id.pow m).mul ?_
    refine DifferentiableAt.fun_finset_prod fun p _ => ?_
    refine DifferentiableAt.div ?_ ?_ (hden u hu p)
    · exact (differentiableAt_const _).sub ((differentiableAt_id.pow _).mul (differentiableAt_const _))
    · exact (differentiableAt_const _).sub
        ((differentiableAt_const _).mul ((differentiableAt_id.pow _).mul (differentiableAt_const _)))
  have h0 : g 0 = if m = 0 then 1 else 0 := by
    have hp : ∏ p ∈ prs n, (1 - (0 : ℂ) ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ))) /
        (1 - (t : ℂ) * ((0 : ℂ) ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ)))) = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      have hlt : (p.1 : ℕ) < (p.2 : ℕ) := (Finset.mem_filter.mp hp).2
      have hk : (p.2 : ℕ) - (p.1 : ℕ) ≠ 0 := by omega
      simp [zero_pow hk]
    simp only [hg, hp, mul_one]
    split_ifs with hm
    · simp [hm]
    · exact zero_pow hm
  have hs : ∀ s : UnitAddCircle, ((AddCircle.toCircle s : Circle) : ℂ) ^ m *
      half (t : ℂ) (fun i => Circle.toUnits (AddCircle.toCircle s) ^ (c - (i : ℕ)) * z i)
      = g ((AddCircle.toCircle s : Circle) : ℂ) := by
    intro s
    simp only [hg, half]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    have hlt : (p.1 : ℕ) < (p.2 : ℕ) := (Finset.mem_filter.mp hp).2
    have hu : ((AddCircle.toCircle s : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have key := ratio_eq _ hu c p.1 p.2 hlt (z p.1 : ℂ) (z p.2 : ℂ)
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Circle.toUnits_apply, Units.val_mk0]
    rw [key]
  simp_rw [hs]
  rw [circle_mean g hd, h0]
