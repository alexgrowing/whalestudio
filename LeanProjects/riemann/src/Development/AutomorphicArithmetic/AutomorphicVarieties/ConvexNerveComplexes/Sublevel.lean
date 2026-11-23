import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.sublevel :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {q : Y → E →L[ℝ] ℝ} {T : Set E}, Good q T → ∀ x ∈ posDual T, ∀ c : ℝ, IsCompact {h | h ∈ poly q ∧ x h ≤ c} := by
  intro E Y _ _ _ q T hG x hx c
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  have hpoly : IsClosed (poly q) := by
    have e : poly q = ⋂ y, {h : E | 1 ≤ q y h} := by
      ext h
      simp [poly]
    rw [e]
    exact isClosed_iInter fun y => isClosed_le continuous_const (q y).continuous
  have hcl : IsClosed {h : E | h ∈ poly q ∧ x h ≤ c} :=
    hpoly.inter (isClosed_le x.continuous continuous_const)
  have hK : IsCompact (Metric.sphere (0 : E) 1 ∩ T) :=
    (isCompact_sphere 0 1).inter_right hG.closed
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ k ∈ Metric.sphere (0 : E) 1 ∩ T, m ≤ x k := by
    rcases (Metric.sphere (0 : E) 1 ∩ T).eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, ?_⟩
      rw [he]
      intro k hk
      exact absurd hk (Set.notMem_empty k)
    · obtain ⟨k0, hk0, hmin⟩ := hK.exists_isMinOn hne x.continuous.continuousOn
      refine ⟨x k0, ?_, fun k hk => hmin hk⟩
      have hk0n : k0 ≠ 0 := by
        intro h0
        have hs := hk0.1
        rw [h0] at hs
        simp at hs
      exact hx k0 hk0.2 hk0n
  apply Metric.isCompact_of_isClosed_isBounded hcl
  refine (Metric.isBounded_closedBall (x := (0 : E)) (r := |c| / m)).subset ?_
  intro h hh
  rw [Metric.mem_closedBall, dist_zero_right]
  by_cases h0 : h = 0
  · rw [h0, norm_zero]
    positivity
  · have hn : 0 < ‖h‖ := norm_pos_iff.mpr h0
    have hT : h ∈ T := hG.sub hh.1
    have hk : ‖h‖⁻¹ • h ∈ Metric.sphere (0 : E) 1 ∩ T := by
      refine ⟨?_, hG.smul_mem _ (inv_pos.mpr hn) h hT⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have h2 := hm _ hk
    rw [map_smul, smul_eq_mul] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 hn.le
    rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul] at h3
    rw [le_div_iff₀ hm0]
    nlinarith [hh.2, le_abs_self c]
