import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.MonicFintype

open Polynomial Finset

noncomputable section

namespace PI.SqfDivDeg.W

theorem second_pair {g : ℕ} [Fact g.Prime] {q h : (ZMod g)[X]} (hq : q.Monic) (hh : h.Monic)
    (hs : Squarefree (q * h)) {x y : ZMod g} (hx : q.IsRoot x) (hy : h.IsRoot y) :
    ((X - C y) * (q /ₘ (X - C x))).Monic ∧ ((X - C x) * (h /ₘ (X - C y))).Monic ∧
    ((X - C y) * (q /ₘ (X - C x))).natDegree = q.natDegree ∧
    ((X - C x) * (h /ₘ (X - C y))).natDegree = h.natDegree ∧
    ((X - C y) * (q /ₘ (X - C x))) * ((X - C x) * (h /ₘ (X - C y))) = q * h ∧
    (X - C y) * (q /ₘ (X - C x)) ≠ q := by
  have hq' : (X - C x) * (q /ₘ (X - C x)) = q := mul_divByMonic_eq_iff_isRoot.mpr hx
  have hh' : (X - C y) * (h /ₘ (X - C y)) = h := mul_divByMonic_eq_iff_isRoot.mpr hy
  have mq : (q /ₘ (X - C x)).Monic :=
    (monic_X_sub_C x).of_mul_monic_left (by rw [hq']; exact hq)
  have mh : (h /ₘ (X - C y)).Monic :=
    (monic_X_sub_C y).of_mul_monic_left (by rw [hh']; exact hh)
  have dq : q.natDegree = 1 + (q /ₘ (X - C x)).natDegree := by
    conv_lhs => rw [← hq']
    rw [(monic_X_sub_C x).natDegree_mul mq, natDegree_X_sub_C]
  have dh : h.natDegree = 1 + (h /ₘ (X - C y)).natDegree := by
    conv_lhs => rw [← hh']
    rw [(monic_X_sub_C y).natDegree_mul mh, natDegree_X_sub_C]
  refine ⟨(monic_X_sub_C y).mul mq, (monic_X_sub_C x).mul mh, ?_, ?_, ?_, ?_⟩
  · rw [(monic_X_sub_C y).natDegree_mul mq, natDegree_X_sub_C, dq]
  · rw [(monic_X_sub_C x).natDegree_mul mh, natDegree_X_sub_C, dh]
  · calc (X - C y) * (q /ₘ (X - C x)) * ((X - C x) * (h /ₘ (X - C y)))
        = ((X - C x) * (q /ₘ (X - C x))) * ((X - C y) * (h /ₘ (X - C y))) := by ring
      _ = q * h := by rw [hq', hh']
  · intro heq
    have hqy : (X - C y) ∣ q := ⟨_, heq.symm⟩
    have hhy : (X - C y) ∣ h := dvd_iff_isRoot.mpr hy
    exact not_isUnit_X_sub_C y (hs _ (mul_dvd_mul hqy hhy))

theorem fibre_nonempty {g r a : ℕ} [Fact g.Prime] (har : a ≤ r) {f : (ZMod g)[X]}
    (hf : PI.SqfLab.Eiv g r a f) :
    ∃ q h, q ∈ Mon g a ∧ h ∈ Mon g (r - a) ∧ q * h = f := by
  obtain ⟨⟨hmon, hdeg, -⟩, -, q, hqf, hqa⟩ := hf
  have hf0 : f ≠ 0 := hmon.ne_zero
  have hq0 : q ≠ 0 := by rintro rfl; exact hf0 (zero_dvd_iff.mp hqf)
  obtain ⟨k, hk⟩ := hqf
  have hl : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq0
  have m1 : (q * C (q.leadingCoeff)⁻¹).Monic := monic_mul_leadingCoeff_inv hq0
  have d1 : (q * C (q.leadingCoeff)⁻¹).natDegree = a := by
    rw [natDegree_mul_C (inv_ne_zero hl), hqa]
  have e : (q * C (q.leadingCoeff)⁻¹) * (C q.leadingCoeff * k) = f := by
    rw [hk]
    calc q * C (q.leadingCoeff)⁻¹ * (C q.leadingCoeff * k)
        = q * (C ((q.leadingCoeff)⁻¹ * q.leadingCoeff)) * k := by rw [C_mul]; ring
      _ = q * k := by rw [inv_mul_cancel₀ hl, C_1, mul_one]
  have m2 : (C q.leadingCoeff * k).Monic := m1.of_mul_monic_left (by rw [e]; exact hmon)
  have d2 : (C q.leadingCoeff * k).natDegree = r - a := by
    have := m1.natDegree_mul m2
    rw [e, hdeg, d1] at this
    omega
  exact ⟨_, _, mem_Mon.mpr ⟨m1, d1⟩, mem_Mon.mpr ⟨m2, d2⟩, e⟩

theorem mainCount : MainCount := by
  intro g r _ a har T hT
  classical
  let P := Mon g a ×ˢ Mon g (r - a)
  let F : (ZMod g)[X] → Finset ((ZMod g)[X] × (ZMod g)[X]) :=
    fun f => P.filter (fun p => p.1 * p.2 = f)
  let G : (ZMod g)[X] × (ZMod g)[X] → Prop :=
    fun p => (∃ x : ZMod g, p.1.IsRoot x) ∧ (∃ y : ZMod g, p.2.IsRoot y)
  let b : (ZMod g)[X] × (ZMod g)[X] → ℝ := fun p => if G p then 1 / 2 else 1
  have bnn : ∀ p, 0 ≤ b p := fun p => by simp only [b]; split_ifs <;> norm_num
  have key : ∀ f ∈ T, (1 : ℝ) ≤ ∑ p ∈ F f, b p := by
    intro f hf
    obtain ⟨q, h, hq, hh, hqh⟩ := fibre_nonempty har (hT f hf)
    have hpq : (q, h) ∈ F f := by simp [F, P, hq, hh, hqh]
    by_cases hG : G (q, h)
    · obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hG
      have hs : Squarefree (q * h) := hqh ▸ (hT f hf).2.1
      obtain ⟨m1, m2, d1, d2, e, ne⟩ :=
        second_pair (mem_Mon.mp hq).1 (mem_Mon.mp hh).1 hs hx hy
      have hp' : ((X - C y) * (q /ₘ (X - C x)), (X - C x) * (h /ₘ (X - C y))) ∈ F f := by
        simp only [F, P, mem_filter, mem_product, mem_Mon]
        exact ⟨⟨⟨m1, d1.trans (mem_Mon.mp hq).2⟩, ⟨m2, d2.trans (mem_Mon.mp hh).2⟩⟩,
          e.trans hqh⟩
      have hG' : G ((X - C y) * (q /ₘ (X - C x)), (X - C x) * (h /ₘ (X - C y))) :=
        ⟨⟨y, by simp⟩, ⟨x, by simp⟩⟩
      have hG0 : G (q, h) := ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      have hne : ((X - C y) * (q /ₘ (X - C x)), (X - C x) * (h /ₘ (X - C y))) ≠ (q, h) :=
        fun h' => ne (congrArg Prod.fst h')
      have hsub : ∑ p ∈ ({((X - C y) * (q /ₘ (X - C x)), (X - C x) * (h /ₘ (X - C y))),
          (q, h)} : Finset _), b p ≤ ∑ p ∈ F f, b p := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [mem_insert, mem_singleton] at hp
          rcases hp with rfl | rfl
          · exact hp'
          · exact hpq
        · intro p _ _; exact bnn p
      rw [sum_pair hne] at hsub
      simp only [b, if_pos hG', if_pos hG0] at hsub
      linarith
    · have : b (q, h) ≤ ∑ p ∈ F f, b p :=
        single_le_sum (f := b) (fun p _ => bnn p) hpq
      simp only [b, if_neg hG] at this
      exact this
  have hdisj : Set.PairwiseDisjoint (↑T) F := by
    intro f _ f' _ hff'
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    simp only [F, mem_filter] at hp hp'
    exact hff' (hp.2.symm.trans hp'.2)
  have h1 : (T.card : ℝ) ≤ ∑ p ∈ T.biUnion F, b p := by
    rw [sum_biUnion hdisj]
    calc (T.card : ℝ) = ∑ f ∈ T, (1 : ℝ) := by simp
      _ ≤ _ := sum_le_sum key
  have h2 : ∑ p ∈ T.biUnion F, b p ≤ ∑ p ∈ P, b p := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨f, -, hpf⟩ := mem_biUnion.mp hp
      exact (mem_filter.mp hpf).1
    · intro p _ _; exact bnn p
  have h3 : ∑ p ∈ P, b p = (P.card : ℝ) - ((P.filter G).card : ℝ) / 2 := by
    simp only [b]
    rw [sum_ite]
    simp only [sum_const, nsmul_eq_mul]
    have hc := card_filter_add_card_filter_not (s := P) (fun p => G p)
    have h' : ((P.filter G).card : ℝ) + ((P.filter (fun p => ¬ G p)).card : ℝ) = P.card := by
      exact_mod_cast hc
    linarith
  have h4 : P.filter G = Rt g a ×ˢ Rt g (r - a) := by
    ext ⟨q, h⟩
    simp only [P, G, Rt, mem_filter, mem_product]
    tauto
  have h5 : (P.card : ℝ) = (g : ℝ) ^ r := by
    simp only [P, card_product, card_Mon]
    push_cast
    rw [← pow_add]
    congr 1
    omega
  rw [h4, h5, card_product] at h3
  push_cast at h3
  linarith

end PI.SqfDivDeg.W
