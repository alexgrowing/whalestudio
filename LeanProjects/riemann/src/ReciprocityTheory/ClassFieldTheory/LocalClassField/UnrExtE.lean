import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem exists_closest {M : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hM : FiniteDimensional ℚ_[p] M) (x : PadicAlgCl p) :
    ∃ m0 ∈ M, ∀ m ∈ M, ‖x - m0‖ ≤ ‖x - m‖ := by
  have : ProperSpace M := FiniteDimensional.proper ℚ_[p] M
  have hc : IsCompact (Metric.closedBall (0 : M) ‖x‖) := isCompact_closedBall 0 ‖x‖
  have hcont : Continuous (fun m : M => ‖x - (m : PadicAlgCl p)‖) :=
    (continuous_const.sub continuous_subtype_val).norm
  have hne : (Metric.closedBall (0 : M) ‖x‖).Nonempty :=
    ⟨0, Metric.mem_closedBall_self (norm_nonneg x)⟩
  obtain ⟨m0, hm0, hmin⟩ := hc.exists_isMinOn hne hcont.continuousOn
  have hmin' : ∀ m : M, m ∈ Metric.closedBall (0 : M) ‖x‖ →
      ‖x - (m0 : PadicAlgCl p)‖ ≤ ‖x - (m : PadicAlgCl p)‖ := fun m hm => hmin hm
  have hle0 : ‖x - (m0 : PadicAlgCl p)‖ ≤ ‖x‖ := by
    have h2 := hmin' 0 (Metric.mem_closedBall_self (norm_nonneg x))
    rwa [ZeroMemClass.coe_zero, sub_zero] at h2
  refine ⟨m0, m0.2, fun m hm => ?_⟩
  by_cases hmx : ‖m‖ ≤ ‖x‖
  · exact hmin' ⟨m, hm⟩ (by rw [mem_closedBall_zero_iff]; exact hmx)
  · rw [not_le] at hmx
    refine hle0.trans ?_
    by_contra hlt
    rw [not_le] at hlt
    have e : m = x - (x - m) := by ring
    have h3 : ‖m‖ ≤ max ‖x‖ ‖x - m‖ := by
      conv_lhs => rw [e]
      exact UnramifiedExtensions.norm_sub_le_max' _ _
    exact absurd (h3.trans (max_le le_rfl hlt.le)) (not_le.2 hmx)

theorem le_of_resK_le_of_norm {M L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hM : FiniteDimensional ℚ_[p] M) (hML : M ≤ L) (hres : resK p L ≤ resK p M)
    (h : ∀ x ∈ L, ∃ y ∈ M, ‖x‖ = ‖y‖) : L ≤ M := by
  intro x hx
  obtain ⟨m0, hm0, hmin⟩ := exists_closest p hM x
  by_contra hxM
  have hy0 : x - m0 ≠ 0 := fun h0 => hxM (by rw [sub_eq_zero.1 h0]; exact hm0)
  have hyL : x - m0 ∈ L := L.sub_mem hx (hML hm0)
  obtain ⟨k, hk, hyk⟩ := h _ hyL
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [norm_zero, norm_eq_zero] at hyk
    exact hy0 hyk
  have hkn : 0 < ‖k‖ := norm_pos_iff.2 hk0
  have h1 : ‖(x - m0) / k‖ = 1 := by rw [norm_div, hyk, div_self hkn.ne']
  have hmem : IsLocalRing.residue (Obar p) ⟨(x - m0) / k, mem_Obar_iff.2 h1.le⟩ ∈ resK p L :=
    (mem_resK_iff p L _).2 ⟨_, L.div_mem hyL (hML hk), rfl⟩
  obtain ⟨z, hz, hzr⟩ := (mem_resK_iff p M _).1 (hres hmem)
  rw [residue_eq_iff] at hzr
  have hzr' : ‖(z : PadicAlgCl p) - (x - m0) / k‖ < 1 := hzr
  have hlt : ‖x - (m0 + k * (z : PadicAlgCl p))‖ < ‖x - m0‖ := by
    have e : x - (m0 + k * (z : PadicAlgCl p)) = -(k * ((z : PadicAlgCl p) - (x - m0) / k)) := by
      rw [mul_sub, mul_div_cancel₀ _ hk0]
      ring
    rw [e, norm_neg, norm_mul, hyk]
    calc ‖k‖ * ‖(z : PadicAlgCl p) - (x - m0) / k‖ < ‖k‖ * 1 :=
          mul_lt_mul_of_pos_left hzr' hkn
      _ = ‖k‖ := mul_one _
  exact absurd hlt (not_lt.2 (hmin _ (M.add_mem hm0 (M.mul_mem hk hz))))

theorem eq_Kn_of_norm (hK : FiniteDimensional ℚ_[p] K) {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hKL : K ≤ L) {n : ℕ} (hn : 0 < n)
    (hdeg : Module.finrank ℚ_[p] L = n * Module.finrank ℚ_[p] K)
    (h : ∀ x ∈ L, ∃ y ∈ K, ‖x‖ = ‖y‖) : L = Kn p K n := by
  have hd : 0 < Module.finrank ℚ_[p] K := Module.finrank_pos
  have hL : FiniteDimensional ℚ_[p] L :=
    Module.finite_of_finrank_pos (by rw [hdeg]; exact Nat.mul_pos hn hd)
  obtain ⟨f, hf, hq, -⟩ := qK_le_pow_finrank p K hK hL hKL
  have hM : FiniteDimensional ℚ_[p] (Kn p K f) := finiteDimensional_Kn p K hK hf
  have hML : Kn p K f ≤ L := Kn_le_of_qK p K hK hL hKL (n := f) (m := 1) (by rw [mul_one]; exact hq)
  have hres : resK p L ≤ resK p (Kn p K f) := by
    have hfin : Finite (resK p L) := finite_resK p L hL
    have hsub : (resK p (Kn p K f) : Set (kbar p)) ⊆ (resK p L : Set (kbar p)) := resK_mono p hML
    have hcard : (resK p L : Set (kbar p)).ncard ≤ (resK p (Kn p K f) : Set (kbar p)).ncard := by
      have e1 : (resK p L : Set (kbar p)).ncard = qK p L := (Nat.card_coe_set_eq _).symm
      have e2 : (resK p (Kn p K f) : Set (kbar p)).ncard = qK p (Kn p K f) :=
        (Nat.card_coe_set_eq _).symm
      rw [e1, e2, hq, qK_Kn p K hK hf]
    have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
    intro c hc
    have : c ∈ (resK p (Kn p K f) : Set (kbar p)) := by rw [heq]; exact hc
    exact this
  have hLM : L = Kn p K f :=
    le_antisymm (le_of_resK_le_of_norm p hM hML hres
      (fun x hx => by
        obtain ⟨y, hy, hxy⟩ := h x hx
        exact ⟨y, le_Kn p K f hy, hxy⟩)) hML
  have hfn : f = n := by
    have h1 := finrank_Kn p K hK hf
    rw [← hLM, hdeg] at h1
    exact (Nat.eq_of_mul_eq_mul_right hd h1).symm
  rw [hLM, hfn]

end ReciprocityTheory.DiscreteGroups.LocalClassField
