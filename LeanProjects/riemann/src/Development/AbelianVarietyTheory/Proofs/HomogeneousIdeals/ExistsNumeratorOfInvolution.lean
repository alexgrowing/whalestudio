import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric

open Filter PeriodPair Polynomial
open scoped Topology

noncomputable section

namespace GlobalTheory

theorem exists_numerator_of_involution {F ι : Type*} [Field F] [CharZero F] [Fintype ι]
    (σ : ι → ι) (hσ : ∀ t, σ (σ t) = t) (p a b : ι → F)
    (hp : ∀ s t, p s = p t ↔ s = t ∨ s = σ t) (hb : ∀ t, b (σ t) = b t)
    (hb0 : ∀ t, b t = 0 ↔ σ t = t) (ha : ∀ t, σ t = t → a t ≠ 0)
    (R : Subring F[X]) (hX : X ∈ R) (hR : ∀ t, C (p t) ∈ R ∧ C (a t) ∈ R ∧ C (b t) ∈ R) :
    ∃ A ∈ R, A.Monic ∧ A.natDegree = Fintype.card ι + 1 ∧ IsCoprime A (∏ t, (X - C (p t))) ∧
      ∀ x, (∀ t, x ≠ p t) → A.eval x =
        (∏ t, (x - p t)) * (x + ∑ t, (a t / (x - p t) + b t / (x - p t) ^ 2)) := by
  classical
  set D : F[X] := ∏ t, (X - C (p t)) with hD
  let E : ι → F[X] := fun t ↦ ∏ s ∈ (Finset.univ.erase t).erase (σ t), (X - C (p s))
  let u : ι → F[X] := fun t ↦ if σ t = t then 1 else X - C (p t)
  have hpσ : ∀ t, p (σ t) = p t := fun t ↦ (hp _ _).mpr (.inr rfl)
  have hDE : ∀ t, D = (X - C (p t)) * (u t * E t) := fun t ↦ by
    rw [hD, ← Finset.mul_prod_erase _ _ (Finset.mem_univ t)]
    congr 1
    by_cases h : σ t = t
    · simp [u, E, h]
    · rw [← Finset.mul_prod_erase _ _ (a := σ t) (by simp [h])]
      simp [u, E, h, hpσ]
  have hDm : D.Monic := monic_prod_of_monic _ _ fun t _ ↦ monic_X_sub_C _
  have hEm : ∀ t, (E t).Monic := fun t ↦ monic_prod_of_monic _ _ fun t _ ↦ monic_X_sub_C _
  have hum : ∀ t, (u t).Monic := fun t ↦ by
    simp only [u]; split_ifs; exacts [monic_one, monic_X_sub_C _]
  have hDd : D.natDegree = Fintype.card ι := by
    rw [hD, natDegree_prod_of_monic _ _ fun t _ ↦ monic_X_sub_C _]; simp
  have hXD : (X * D).natDegree = Fintype.card ι + 1 := by
    rw [monic_X.natDegree_mul hDm, hDd, natDegree_X, add_comm]
  have hlt : (∑ t, (C (a t) * u t + C (b t)) * E t).natDegree < (X * D).natDegree := by
    rw [hXD, Nat.lt_succ_iff, ← hDd]
    refine natDegree_sum_le_of_forall_le _ _ fun t _ ↦ natDegree_mul_le.trans ?_
    rw [hDE t, (monic_X_sub_C _).natDegree_mul ((hum t).mul (hEm t)),
      (hum t).natDegree_mul (hEm t), natDegree_add_C]
    have := natDegree_C_mul_le (a t) (u t)
    omega
  refine ⟨X * D + ∑ t, (C (a t) * u t + C (b t)) * E t, ?_,
    (monic_X.mul hDm).add_of_left (degree_lt_degree hlt),
    by rw [natDegree_add_eq_left_of_natDegree_lt hlt, hXD], ?_, fun x hx ↦ ?_⟩
  · refine add_mem (mul_mem hX (prod_mem fun t _ ↦ sub_mem hX (hR t).1))
      (sum_mem fun t _ ↦ mul_mem (add_mem (mul_mem (hR t).2.1 ?_) (hR t).2.2)
        (prod_mem fun t _ ↦ sub_mem hX (hR t).1))
    simp only [u]; split_ifs; exacts [one_mem _, sub_mem hX (hR t).1]
  · refine IsCoprime.prod_right fun t _ ↦
      ((irreducible_X_sub_C (p t)).coprime_iff_not_dvd.mpr ?_).symm
    rw [dvd_iff_isRoot, IsRoot.def]
    have h0 : D.eval (p t) = 0 := by rw [hDE t]; simp
    have h1 : ∀ s, s ≠ t → s ≠ σ t → ((C (a s) * u s + C (b s)) * E s).eval (p t) = 0 :=
      fun s h h' ↦ by
        rw [eval_mul, eval_prod, Finset.prod_eq_zero (i := t), mul_zero]
        · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          exact ⟨fun e ↦ h' (by rw [e, hσ]), h.symm⟩
        · simp
    have h2 : (E t).eval (p t) ≠ 0 := by
      rw [eval_prod, Finset.prod_ne_zero_iff]
      intro s hs
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hs
      simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
      exact fun e ↦ by have := (hp _ _).mp e.symm; tauto
    rw [eval_add, eval_mul, h0, mul_zero, zero_add, eval_finsetSum]
    by_cases h : σ t = t
    · rw [Finset.sum_eq_single t (fun s _ hs ↦ h1 s hs (by rwa [h])) (by simp)]
      simp [u, h, (hb0 t).mpr h, ha t h, h2]
    · rw [Finset.sum_eq_add t (σ t) (Ne.symm h) (fun s _ hs ↦ h1 s hs.1 hs.2) (by simp) (by simp)]
      have h3 : E (σ t) = E t := by simp only [E, hσ]; rw [Finset.erase_right_comm]
      have h4 : b t ≠ 0 := (hb0 t).not.mpr h
      simp [u, h, hσ, Ne.symm h, hpσ, hb, h3, h4, h2, ← two_mul]
  · have h0 : D.eval x = ∏ t, (x - p t) := by simp [hD, eval_prod]
    rw [← h0, mul_add, eval_add, eval_mul, eval_X, mul_comm, eval_finsetSum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    have := sub_ne_zero.mpr (hx t)
    rw [hDE t]
    by_cases h : σ t = t
    · simp [u, h, (hb0 t).mpr h]
      field_simp
    · simp [u, h]
      field_simp

variable {L L' : PeriodPair} {α : ℂ}

theorem weierstrassP_mul_eq_sum (hα0 : α ≠ 0) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice)
    {ι : Type*} [Fintype ι] (r : ι → ℂ) (h₁ : ∀ t, α * r t ∈ L'.lattice)
    (h₂ : ∀ s t, r s - r t ∈ L.lattice → s = t)
    (h₃ : ∀ m, α * m ∈ L'.lattice → ∃ t, m - r t ∈ L.lattice) (z : ℂ) :
    α ^ 2 * ℘[L'] (α * z) = ∑ t, (℘[L] (z - r t) - ℘[L] (r t)) := by
  let e : ι × L.lattice → L'.lattice := fun x ↦
    ⟨α * (r x.1 + x.2), by rw [mul_add]; exact add_mem (h₁ _) (hα _ x.2.2)⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨s, l⟩ ⟨t, l'⟩ h
      have h0 : r s + l = r t + l' := mul_left_cancel₀ hα0 (congrArg Subtype.val h)
      obtain rfl : s = t := h₂ _ _ (by
        rw [show r s - r t = l' - l by linear_combination h0]; exact sub_mem l'.2 l.2)
      rw [Subtype.ext (add_left_cancel h0)]
    · rintro ⟨m, hm⟩
      obtain ⟨t, ht⟩ := h₃ (α⁻¹ * m) (by rwa [mul_inv_cancel_left₀ hα0])
      exact ⟨⟨t, _, ht⟩, Subtype.ext (by simp [e, hα0])⟩
  have h := (Equiv.ofBijective e he).hasSum_iff.mpr
    ((L'.hasSum_weierstrassP (α * z)).mul_left (α ^ 2))
  refine (h.prod_fiberwise fun t ↦ ?_).unique (hasSum_fintype _)
  rw [← L.weierstrassP_neg (r t)]
  refine ((L.hasSum_weierstrassP (z - r t)).sub (L.hasSum_weierstrassP (-r t))).congr_fun ?_
  intro l
  simp only [e, Equiv.ofBijective_apply, Function.comp_apply, ← mul_sub, mul_pow]
  field_simp
  ring

lemma exists_representatives (hα0 : α ≠ 0) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice) :
    ∃ (Q : Type) (_ : AddCommGroup Q) (_ : Finite Q) (r : Q → ℂ),
      Nat.card Q = (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex
        L'.lattice.toAddSubgroup ∧
      (∀ t, α * r t ∈ L'.lattice) ∧ (∀ s t, r s - r t ∈ L.lattice ↔ s = t) ∧
      (∀ s t, r s + r t ∈ L.lattice ↔ s = -t) ∧ (∀ t, r t ∈ L.lattice ↔ t = 0) ∧
      (∀ m, α * m ∈ L'.lattice → ∃ t, m - r t ∈ L.lattice) := by
  let N : Submodule ℤ L'.lattice := (L.lattice.map (LinearMap.mulLeft ℤ α)).submoduleOf L'.lattice
  have hle : L.lattice.map (LinearMap.mulLeft ℤ α) ≤ L'.lattice := by
    rintro _ ⟨l, hl, rfl⟩; exact hα l hl
  have hN : Module.finrank ℤ N = Module.finrank ℤ L'.lattice := by
    rw [(Submodule.submoduleOfEquivOfLe hle).finrank_eq, ← (Submodule.equivMapOfInjective _
      (mul_right_injective₀ hα0) L.lattice).finrank_eq, finrank_lattice, finrank_lattice]
  have key : ∀ x : L'.lattice, α⁻¹ * x ∈ L.lattice ↔ N.mkQ x = 0 := fun x ↦ by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · exact fun h ↦ ⟨_, h, by simp [hα0]⟩
    · rintro ⟨l, hl, e⟩
      have e' : α * l = x := e
      rw [← e', inv_mul_cancel_left₀ hα0]
      exact hl
  choose o ho using N.mkQ_surjective
  refine ⟨L'.lattice ⧸ N, inferInstance, Submodule.finiteQuotientOfFreeOfRankEq N hN,
    fun t ↦ α⁻¹ * o t, rfl, fun t ↦ by simp [hα0], fun s t ↦ ?_, fun s t ↦ ?_, fun t ↦ ?_,
    fun m hm ↦ ⟨N.mkQ ⟨_, hm⟩, ?_⟩⟩
  · rw [← mul_sub, ← Submodule.coe_sub, key, map_sub, ho, ho, sub_eq_zero]
  · rw [← mul_add, ← Submodule.coe_add, key, map_add, ho, ho, add_eq_zero_iff_eq_neg]
  · rw [key, ho]
  · have := (key (⟨_, hm⟩ - o (N.mkQ ⟨_, hm⟩))).mpr (by rw [map_sub, ho, sub_self])
    simpa [mul_sub, hα0] using this

theorem exists_weierstrassP_mul_eq_div (hα0 : α ≠ 0) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice)
    (k : Subfield ℂ) (h₂ : L.g₂ ∈ k) (h₃ : L.g₃ ∈ k) (hαk : α ∈ k)
    (hk : ∀ t ∉ L.lattice, α * t ∈ L'.lattice → ℘[L] t ∈ k) :
    ∃ A D : ℂ[X], (∀ i, A.coeff i ∈ k) ∧ (∀ i, D.coeff i ∈ k) ∧ D.Monic ∧
      A.leadingCoeff = (α ^ 2)⁻¹ ∧ IsCoprime A D ∧
      A.natDegree = (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex
        L'.lattice.toAddSubgroup ∧
      D.natDegree + 1 = A.natDegree ∧
      (∀ z ∉ L.lattice, D.eval (℘[L] z) = 0 ↔ α * z ∈ L'.lattice) ∧
      ∀ z, α * z ∉ L'.lattice → ℘[L'] (α * z) = A.eval (℘[L] z) / D.eval (℘[L] z) := by
  classical
  obtain ⟨Q, _, _, r, hc, r1, r2, r3, r4, r5⟩ := exists_representatives hα0 hα
  have := Fintype.ofFinite Q
  let ι := {t : Q // t ≠ 0}
  have hr : ∀ t : ι, r t ∉ L.lattice := fun t ↦ (r4 t).not.mpr t.2
  let σ : ι → ι := fun t ↦ ⟨-t, neg_ne_zero.mpr t.2⟩
  have hneg : ∀ t : Q, ∃ l : L.lattice, r (-t) = -r t + l := fun t ↦
    ⟨⟨_, (r3 (-t) t).mpr rfl⟩, by simp⟩
  have hC : ∀ c ∈ k, C c ∈ liftsRing k.subtype := fun c hc ↦ C'_mem_lifts ⟨⟨c, hc⟩, rfl⟩
  have hpk : ∀ t : ι, ℘[L] (r t) ∈ k := fun t ↦ hk _ (hr t) (r1 t)
  have hn : ∀ n : ℕ, (n : ℂ) ∈ k := fun n ↦ natCast_mem k n
  obtain ⟨A, hAk, hAm, hAd, hAc, hAe⟩ := exists_numerator_of_involution σ
    (fun t ↦ Subtype.ext (neg_neg _)) (fun t ↦ ℘[L] (r t))
    (fun t ↦ (6 * ℘[L] (r t) ^ 2 - L.g₂ / 2) / 2) (fun t ↦ ℘'[L] (r t) ^ 2 / 2)
    (fun s t ↦ by
      rw [weierstrassP_eq_iff L (hr s) (hr t), r2, r3, Subtype.ext_iff, Subtype.ext_iff])
    (fun t ↦ by obtain ⟨l, hl⟩ := hneg t; simp [σ, hl])
    (fun t ↦ by
      rw [Subtype.ext_iff, eq_comm (b := t.1), ← r3, ← derivWeierstrassP_eq_zero_iff L (hr t)]
      simp)
    (fun t ht ↦ div_ne_zero (weierstrassP_second_ne_zero L (hr t) (by
      rwa [Subtype.ext_iff, eq_comm (b := t.1), ← r3,
        ← derivWeierstrassP_eq_zero_iff L (hr t)] at ht)) two_ne_zero)
    (liftsRing k.subtype) (X_mem_lifts _) (fun t ↦ ⟨hC _ (hpk t),
      hC _ (div_mem (sub_mem (mul_mem (hn 6) (pow_mem (hpk t) 2)) (div_mem h₂ (hn 2))) (hn 2)),
      hC _ (div_mem (by
        rw [L.derivWeierstrassP_sq _ (hr t)]
        exact sub_mem (sub_mem (mul_mem (hn 4) (pow_mem (hpk t) 3)) (mul_mem h₂ (hpk t))) h₃)
        (hn 2))⟩)
  have hcoeff : ∀ P ∈ liftsRing k.subtype, ∀ i, P.coeff i ∈ k := fun P hP i ↦ by
    obtain ⟨c, hc⟩ := (lifts_iff_coeff_lifts P).mp hP i
    exact hc ▸ c.2
  have hα2 : (α ^ 2)⁻¹ ≠ 0 := by simp [hα0]
  have hcard : Fintype.card ι + 1 = Nat.card Q := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      Nat.sub_add_cancel Fintype.card_pos]
  have hD0 : ∀ z ∉ L.lattice, (∃ t : ι, ℘[L] z = ℘[L] (r t)) ↔ α * z ∈ L'.lattice := fun z hz ↦ by
    constructor
    · rintro ⟨t, ht⟩
      rcases (weierstrassP_eq_iff L hz (hr t)).mp ht with h | h
      · simpa [mul_sub] using add_mem (hα _ h) (r1 t)
      · simpa [mul_add] using sub_mem (hα _ h) (r1 t)
    · intro h
      obtain ⟨t, ht⟩ := r5 z h
      have ht0 : t ≠ 0 := fun e ↦ hz (by simpa using add_mem ht ((r4 t).mpr e))
      exact ⟨⟨t, ht0⟩, (weierstrassP_eq_iff L hz (hr ⟨t, ht0⟩)).mpr (.inl ht)⟩
  refine ⟨C (α ^ 2)⁻¹ * A, ∏ t : ι, (X - C (℘[L] (r t))),
    hcoeff _ (mul_mem (hC _ (inv_mem (pow_mem hαk 2))) hAk),
    hcoeff _ (prod_mem fun t _ ↦ sub_mem (X_mem_lifts _) (hC _ (hpk t))),
    monic_prod_of_monic _ _ fun t _ ↦ monic_X_sub_C _, by simp [hAm],
    (isCoprime_mul_unit_left_left (isUnit_C.mpr hα2.isUnit) _ _).mpr hAc,
    by rw [natDegree_C_mul hα2, hAd, hcard, hc], ?_, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [natDegree_C_mul hα2, hAd, natDegree_prod_of_monic _ _ fun t _ ↦ monic_X_sub_C _]
    simp
  · rw [← hD0 z hz]
    simp [eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]
  · have hzL : z ∉ L.lattice := fun h ↦ hz (hα z h)
    have hx : ∀ t : ι, ℘[L] z ≠ ℘[L] (r t) := fun t h ↦ hz ((hD0 z hzL).mp ⟨t, h⟩)
    have hP : ∏ t : ι, (℘[L] z - ℘[L] (r t)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun t _ ↦ sub_ne_zero.mpr (hx t)
    have s1 := weierstrassP_mul_eq_sum hα0 hα r r1 (fun s t ↦ (r2 s t).mp) r5 z
    have s2 : α ^ 2 * ℘[L'] (α * z) = ∑ t, (℘[L] (z + r t) - ℘[L] (r t)) := by
      rw [s1]
      refine (Fintype.sum_equiv (Equiv.neg Q) _ _ fun t ↦ ?_).symm
      obtain ⟨l, hl⟩ := hneg t
      simp [hl, ← sub_sub]
    have s3 : 2 * (α ^ 2 * ℘[L'] (α * z)) =
        ∑ t, (℘[L] (z + r t) + ℘[L] (z - r t) - 2 * ℘[L] (r t)) := by
      rw [two_mul]
      nth_rw 1 [s1]
      rw [s2, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ ↦ by ring
    have h0 := (r4 0).mpr rfl
    rw [Fintype.sum_eq_add_sum_subtype_ne _ 0, L.weierstrassP_add_coe z ⟨_, h0⟩,
      L.weierstrassP_sub_coe z ⟨_, h0⟩, L.weierstrassP_coe ⟨_, h0⟩,
      Finset.sum_congr rfl fun (t : ι) _ ↦ weierstrassP_add_add_sub L hzL (hr t) (hx t)] at s3
    have s4 : ∑ t : ι, ((6 * ℘[L] (r t) ^ 2 - L.g₂ / 2) / (℘[L] z - ℘[L] (r t)) +
        ℘'[L] (r t) ^ 2 / (℘[L] z - ℘[L] (r t)) ^ 2) =
        2 * ∑ t : ι, ((6 * ℘[L] (r t) ^ 2 - L.g₂ / 2) / 2 / (℘[L] z - ℘[L] (r t)) +
        ℘'[L] (r t) ^ 2 / 2 / (℘[L] z - ℘[L] (r t)) ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ ↦ by ring
    rw [s4] at s3
    rw [eval_mul, eval_C, hAe _ hx, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    rw [mul_div_assoc, mul_div_cancel_left₀ _ hP, eq_inv_mul_iff_mul_eq₀ (pow_ne_zero 2 hα0)]
    linear_combination s3 / 2

end GlobalTheory
