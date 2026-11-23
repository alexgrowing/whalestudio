import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CarSumSqZeroOfAnti

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem carKinv_triple₁ {R : Type*} [Ring R] (A B C δ : R) (h1 : C * A + A * C = 0)
    (h2 : B * C + C * B = δ) : A * B * C - C * (A * B) = A * δ := by
  calc A * B * C - C * (A * B) = A * (B * C + C * B) - (C * A + A * C) * B := by noncomm_ring
    _ = A * δ := by rw [h1, h2]; noncomm_ring

theorem carKinv_triple₂ {R : Type*} [Ring R] (A B C δ : R) (h1 : C * A + A * C = δ)
    (h2 : B * C + C * B = 0) : A * B * C - C * (A * B) = -(δ * B) := by
  calc A * B * C - C * (A * B) = A * (B * C + C * B) - (C * A + A * C) * B := by noncomm_ring
    _ = -(δ * B) := by rw [h1, h2]; noncomm_ring

theorem carKinv_sum_mul_comm {R ι κ : Type*} [Ring R] (s : Finset ι) (t : Finset κ)
    (f : ι → κ → R) (X : R) (h : ∑ i ∈ s, ∑ c ∈ t, (f i c * X - X * f i c) = 0) :
    (∑ i ∈ s, ∑ c ∈ t, f i c) * X = X * ∑ i ∈ s, ∑ c ∈ t, f i c := by
  rw [← sub_eq_zero, ← h, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem carKinv_expand {R : Type*} [Ring R] (P Q A S : R) (hQA : Q * A = A * Q)
    (hPS : P * S = S * P) :
    P * Q * (A + S) - (A + S) * (P * Q) = (P * A - A * P) * Q - P * (S * Q - Q * S) := by
  calc P * Q * (A + S) - (A + S) * (P * Q)
      = (P * A - A * P) * Q - P * (S * Q - Q * S) + P * (Q * A - A * Q) + (P * S - S * P) * Q := by
        noncomm_ring
    _ = (P * A - A * P) * Q - P * (S * Q - Q * S) := by
        rw [hQA, hPS, sub_self, sub_self, mul_zero, zero_mul, add_zero, add_zero]

theorem carKinv_E_sgE {E cp cm : Fin n → Fin n → Module.End ℂ W} (hEC : CommutesCAR E cp cm)
    (ε : Fin n → Bool) (a b c d : Fin n) : E c d * sgE ε cp cm a b = sgE ε cp cm a b * E c d := by
  have key : ∀ x y u v, E c d * (cp x y * cm u v) = cp x y * cm u v * E c d := by
    intro x y u v
    rw [← mul_assoc, (hEC c d x y).1, mul_assoc, (hEC c d u v).2, ← mul_assoc]
  unfold sgE
  split_ifs
  · rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => key _ _ _ _
  · rw [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun x _ => key _ _ _ _)
  · simp

theorem carKinv_sg_cp_plus {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (ε : Fin n → Bool) (a b i c : Fin n) (ha : ε a = true) (hb : ε b = true) (hc : ε c = false) :
    sgE ε cp cm a b * cp i c - cp i c * sgE ε cp cm a b = if b = i then cp a c else 0 := by
  have hs : sgE ε cp cm a b = ∑ x ∈ minusIdx ε, cp a x * cm b x := by simp [sgE, ha, hb]
  have hcm : c ∈ minusIdx ε := by simp [minusIdx, hc]
  rw [hs, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun x _ => carKinv_triple₁ _ _ _ _ (hC i c a x).1 (hC b x i c).2.2]
  by_cases hbi : b = i
  · subst hbi
    simp [mul_ite, Finset.sum_ite_eq', hcm]
  · simp [hbi]

theorem carKinv_sg_cp_minus {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (ε : Fin n → Bool) (a b i c : Fin n) (ha : ε a = false) (hb : ε b = false) (hi : ε i = true) :
    sgE ε cp cm a b * cp i c - cp i c * sgE ε cp cm a b = -(if a = c then cp i b else 0) := by
  have hs : sgE ε cp cm a b = -∑ y ∈ plusIdx ε, cp y b * cm y a := by simp [sgE, ha, hb]
  have hip : i ∈ plusIdx ε := by simp [plusIdx, hi]
  have e : ∀ S T : Module.End ℂ W, (-S) * T - T * (-S) = -(S * T - T * S) := fun S T => by noncomm_ring
  rw [hs, e, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun y _ => carKinv_triple₁ _ _ _ _ (hC i c y b).1 (hC y a i c).2.2]
  congr 1
  by_cases hac : a = c
  · subst hac
    simp [mul_ite, Finset.sum_ite_eq', hip]
  · simp [hac]

theorem carKinv_sg_cm_plus {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (ε : Fin n → Bool) (a b i c : Fin n) (ha : ε a = true) (hb : ε b = true) (hc : ε c = false) :
    sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b = -(if i = a then cm b c else 0) := by
  have hs : sgE ε cp cm a b = ∑ x ∈ minusIdx ε, cp a x * cm b x := by simp [sgE, ha, hb]
  have hcm : c ∈ minusIdx ε := by simp [minusIdx, hc]
  rw [hs, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun x _ => carKinv_triple₂ _ _ _ _ (hC i c a x).2.2 (hC b x i c).2.1,
    Finset.sum_neg_distrib]
  congr 1
  by_cases hia : i = a
  · subst hia
    simp [ite_mul, Finset.sum_ite_eq, hcm]
  · simp [hia]

theorem carKinv_sg_cm_minus {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (ε : Fin n → Bool) (a b i c : Fin n) (ha : ε a = false) (hb : ε b = false) (hi : ε i = true) :
    sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b = if c = b then cm i a else 0 := by
  have hs : sgE ε cp cm a b = -∑ y ∈ plusIdx ε, cp y b * cm y a := by simp [sgE, ha, hb]
  have hip : i ∈ plusIdx ε := by simp [plusIdx, hi]
  have e : ∀ S T : Module.End ℂ W, (-S) * T - T * (-S) = -(S * T - T * S) := fun S T => by noncomm_ring
  rw [hs, e, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun y _ => carKinv_triple₂ _ _ _ _ (hC i c y b).2.2 (hC y a i c).2.1,
    Finset.sum_neg_distrib, neg_neg]
  by_cases hcb : c = b
  · subst hcb
    simp [ite_mul, Finset.sum_ite_eq, hip]
  · simp [hcb]

theorem carKinv_term_d {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b i c : Fin n) :
    E c i * cp i c * diagE ε E cp cm a b - diagE ε E cp cm a b * (E c i * cp i c) =
      ((if i = a then E c b else 0) - (if b = c then E a i else 0)) * cp i c -
        E c i * (sgE ε cp cm a b * cp i c - cp i c * sgE ε cp cm a b) := by
  unfold diagE
  rw [carKinv_expand _ _ _ _ (hEC a b i c).1.symm (carKinv_E_sgE hEC ε a b c i), hE c i a b]

theorem carKinv_term_d' {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b i c : Fin n) :
    E i c * cm i c * diagE ε E cp cm a b - diagE ε E cp cm a b * (E i c * cm i c) =
      ((if c = a then E i b else 0) - (if b = i then E a c else 0)) * cm i c -
        E i c * (sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b) := by
  unfold diagE
  rw [carKinv_expand _ _ _ _ (hEC a b i c).2.symm (carKinv_E_sgE hEC ε a b i c), hE i c a b]

theorem dOp_comm_diagE {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b : Fin n) (hab : ε a = ε b) :
    dOp ε E cp * diagE ε E cp cm a b = diagE ε E cp cm a b * dOp ε E cp := by
  unfold dOp
  apply carKinv_sum_mul_comm
  simp_rw [carKinv_term_d hE hEC]
  have hpl : ∀ x, x ∈ plusIdx ε ↔ ε x = true := fun x => by simp [plusIdx]
  have hmi : ∀ x, x ∈ minusIdx ε ↔ ε x = false := fun x => by simp [minusIdx]
  cases hεa : ε a
  ·
    have hεb : ε b = false := by rw [← hab]; exact hεa
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' := (hpl i).1 hi
    have hia : i ≠ a := by rintro rfl; simp_all
    rw [Finset.sum_congr rfl fun c _ => show
        ((if i = a then E c b else 0) - (if b = c then E a i else 0)) * cp i c -
          E c i * (sgE ε cp cm a b * cp i c - cp i c * sgE ε cp cm a b) =
        (if a = c then E a i * cp i b else 0) - (if b = c then E a i * cp i b else 0) by
      rw [carKinv_sg_cp_minus hC ε a b i c hεa hεb hi']
      split_ifs <;> subst_vars <;> (try simp_all) <;> (try noncomm_ring)]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos ((hmi a).2 hεa),
      if_pos ((hmi b).2 hεb), sub_self]
  ·
    have hεb : ε b = true := by rw [← hab]; exact hεa
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c hc => ?_
    have hc' := (hmi c).1 hc
    have hbc : b ≠ c := by rintro rfl; simp_all
    rw [Finset.sum_congr rfl fun i _ => show
        ((if i = a then E c b else 0) - (if b = c then E a i else 0)) * cp i c -
          E c i * (sgE ε cp cm a b * cp i c - cp i c * sgE ε cp cm a b) =
        (if i = a then E c b * cp a c else 0) - (if b = i then E c b * cp a c else 0) by
      rw [carKinv_sg_cp_plus hC ε a b i c hεa hεb hc']
      split_ifs <;> subst_vars <;> (try simp_all) <;> (try noncomm_ring)]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos ((hpl a).2 hεa),
      if_pos ((hpl b).2 hεb), sub_self]

theorem dOp'_comm_diagE {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b : Fin n) (hab : ε a = ε b) :
    dOp' ε E cm * diagE ε E cp cm a b = diagE ε E cp cm a b * dOp' ε E cm := by
  unfold dOp'
  rw [neg_mul, mul_neg, neg_inj]
  apply carKinv_sum_mul_comm
  simp_rw [carKinv_term_d' hE hEC]
  have hpl : ∀ x, x ∈ plusIdx ε ↔ ε x = true := fun x => by simp [plusIdx]
  have hmi : ∀ x, x ∈ minusIdx ε ↔ ε x = false := fun x => by simp [minusIdx]
  cases hεa : ε a
  ·
    have hεb : ε b = false := by rw [← hab]; exact hεa
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' := (hpl i).1 hi
    have hib : b ≠ i := by rintro rfl; simp_all
    rw [Finset.sum_congr rfl fun c _ => show
        ((if c = a then E i b else 0) - (if b = i then E a c else 0)) * cm i c -
          E i c * (sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b) =
        (if c = a then E i b * cm i a else 0) - (if c = b then E i b * cm i a else 0) by
      rw [carKinv_sg_cm_minus hC ε a b i c hεa hεb hi']
      split_ifs <;> subst_vars <;> (try simp_all) <;> (try noncomm_ring)]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos ((hmi a).2 hεa),
      if_pos ((hmi b).2 hεb), sub_self]
  ·
    have hεb : ε b = true := by rw [← hab]; exact hεa
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c hc => ?_
    have hc' := (hmi c).1 hc
    have hca : c ≠ a := by rintro rfl; simp_all
    rw [Finset.sum_congr rfl fun i _ => show
        ((if c = a then E i b else 0) - (if b = i then E a c else 0)) * cm i c -
          E i c * (sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b) =
        (if i = a then E a c * cm b c else 0) - (if b = i then E a c * cm b c else 0) by
      rw [carKinv_sg_cm_plus hC ε a b i c hεa hεb hc']
      split_ifs <;> subst_vars <;> (try simp_all) <;> (try noncomm_ring)]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos ((hpl a).2 hεa),
      if_pos ((hpl b).2 hεb), sub_self]

end ReciprocityTheory.ChartRestriction.DS
