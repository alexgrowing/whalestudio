import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorIsRingHomStatement
open IsLocalRing GlobalTheory.FormalOrigin MvPowerSeries

noncomputable section
namespace GlobalTheory.TaylorInj

theorem foldr_ite {A : Type} {n : ℕ} (D : A → A) (a : Fin n) (f : A) (l : List (Fin n)) :
    l.foldr (fun i g => if i = a then D g else g) f = D^[l.count a] f := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldr_cons, ih, List.count_cons]
    by_cases h : i = a
    · subst h; simp [Function.iterate_succ_apply']
    · simp [h]

theorem iterOp_single {A : Type} {n : ℕ} (ds : Fin n → A → A) (a : Fin n) (f : A) :
    iterOp ds (Finsupp.single a 1) f = ds a f := by
  have e : (fun i g => (ds i)^[Finsupp.single a 1 i] g) = (fun i g => if i = a then ds a g else g) := by
    funext i g
    by_cases h : i = a
    · subst h; simp
    · simp [Finsupp.single_apply, Ne.symm h, h]
  unfold iterOp
  rw [e, foldr_ite, List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange a)]
  rfl

theorem coeff_taylor {A B : Type} [CommRing A] [CommRing B] [Algebra ℚ B] {n : ℕ} (ev : A →+* B)
    (ds : Fin n → A → A) (f : A) (α : Fin n →₀ ℕ) :
    coeff α (taylor ev ds f) = (∏ i, ((α i).factorial : ℚ))⁻¹ • ev (iterOp ds α f) := rfl

theorem degree_eq_one {n : ℕ} {D : Fin n →₀ ℕ} (h : D.degree = 1) : ∃ s, D = Finsupp.single s 1 := by
  have hsum := h
  rw [Finsupp.degree_eq_sum] at hsum
  obtain ⟨s, hs⟩ : ∃ s, D s ≠ 0 := by
    by_contra hc
    push_neg at hc
    simp [hc] at hsum
  refine ⟨s, ?_⟩
  have hle : ∀ t, t ≠ s → D s + D t ≤ 1 := fun t ht => by
    rw [← hsum, ← Finset.sum_pair (Ne.symm ht)]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  ext t
  by_cases ht : t = s
  · subst ht
    have : D t ≤ 1 := h ▸ Finsupp.le_degree t D
    simp only [Finsupp.single_eq_same]
    omega
  · have := hle t ht
    simp only [Finsupp.single_apply, if_neg (Ne.symm ht)]
    omega

section Rel
variable {σ S : Type} [CommRing S]

def Rel (e : ℕ) (F G : MvPowerSeries σ S) : Prop :=
  (e : ℕ∞) ≤ G.order ∧ ((e + 1 : ℕ) : ℕ∞) ≤ (F - G).order

theorem le_order_of_rel {e : ℕ} {F G : MvPowerSeries σ S} (h : Rel e F G) : (e : ℕ∞) ≤ F.order := by
  have : F = G + (F - G) := by ring
  rw [this]
  exact le_trans (le_min h.1 (le_trans (by exact_mod_cast Nat.le_succ e) h.2)) min_order_le_add

theorem rel_mul {a b : ℕ} {F G F' G' : MvPowerSeries σ S} (h : Rel a F G) (h' : Rel b F' G') :
    Rel (a + b) (F * F') (G * G') := by
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ le_order_mul
    push_cast; exact add_le_add h.1 h'.1
  · have e : F * F' - G * G' = (F - G) * F' + G * (F' - G') := by ring
    rw [e]
    refine le_trans (le_min ?_ ?_) min_order_le_add
    · refine le_trans ?_ le_order_mul
      refine le_trans (le_of_eq ?_) (add_le_add h.2 (le_order_of_rel h'))
      push_cast; ring
    · refine le_trans ?_ le_order_mul
      refine le_trans (le_of_eq ?_) (add_le_add h.1 h'.2)
      push_cast; ring

theorem rel_one : Rel 0 (1 : MvPowerSeries σ S) 1 := by
  refine ⟨by simp, by simp⟩

theorem rel_pow {a : ℕ} {F G : MvPowerSeries σ S} (h : Rel a F G) (k : ℕ) :
    Rel (a * k) (F ^ k) (G ^ k) := by
  induction k with
  | zero => simpa using (rel_one (σ := σ) (S := S))
  | succ k ih =>
    rw [pow_succ, pow_succ, Nat.mul_succ]
    exact rel_mul ih h

theorem rel_prod_pow {ι : Type} (s : Finset ι) (F G : ι → MvPowerSeries σ S) (β : ι → ℕ)
    (h : ∀ i, Rel 1 (F i) (G i)) :
    Rel (∑ i ∈ s, β i) (∏ i ∈ s, F i ^ β i) (∏ i ∈ s, G i ^ β i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (rel_one (σ := σ) (S := S))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    have := rel_mul (rel_pow (h i) (β i)) ih
    rwa [one_mul] at this

end Rel

theorem ker_le_span {R A : Type} [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (inc : R →+* A) (ev : A →+* R) (hev : ∀ r, ev (inc r) = r) {n : ℕ}
    (z : Fin n → A) (hz : ∀ i, ev (z i) = 0)
    (hm : maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z)) :
    RingHom.ker ev ≤ Ideal.span (Set.range z) := by
  set K := RingHom.ker ev
  set J := Ideal.span (Set.range z)
  set I := (maximalIdeal R).map inc
  have hJK : J ≤ K := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hz i)
  have key : ∀ y ∈ I, y - inc (ev y) ∈ I * K := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => y - inc (ev y) ∈ I * K) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨r, -, rfl⟩; simp [hev]
    · simp
    · intro x y _ _ hx hy
      have := Ideal.add_mem _ hx hy
      convert this using 1; simp only [map_add]; ring
    · intro a x hx' hx
      have e : a • x - inc (ev (a • x)) = (a - inc (ev a)) * x + inc (ev a) * (x - inc (ev x)) := by
        simp only [smul_eq_mul, map_mul]; ring
      rw [e]
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ hx)
      rw [mul_comm (a - inc (ev a))]; exact Ideal.mul_mem_mul hx' (RingHom.mem_ker.2 (by simp [hev]))
  have hle : K ≤ J ⊔ I • K := by
    intro x hx
    have hxm : x ∈ maximalIdeal A := by
      rw [mem_maximalIdeal, mem_nonunits_iff]; intro hu
      have := hu.map ev; rw [RingHom.mem_ker.1 hx] at this; exact not_isUnit_zero this
    rw [hm, Submodule.mem_sup] at hxm
    obtain ⟨y, hy, w, hw, rfl⟩ := hxm
    have hw0 : ev w = 0 := hJK hw
    have hy0 : ev y = 0 := by
      have := RingHom.mem_ker.1 hx; rwa [map_add, hw0, add_zero] at this
    have := key y hy
    rw [hy0, map_zero, sub_zero] at this
    rw [add_comm]; exact Submodule.add_mem_sup hw this
  have hIj : I ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hm]; exact le_sup_left
  exact Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian K) hIj hle

end GlobalTheory.TaylorInj

namespace GlobalTheory.TaylorInj
section Main
variable {R A : Type} [CommRing R] [Algebra ℚ R] [CommRing A] {n : ℕ}

theorem rel_const (ev : A →+* R) (ds : Fin n → A → A) (T : A →+* MvPowerSeries (Fin n) R)
    (hT : ∀ f, T f = taylor ev ds f) (c : A) : Rel 0 (T c) (C (ev c)) := by
  refine ⟨by simp, ?_⟩
  have h0 : constantCoeff (T c) = ev c := by
    rw [← coeff_zero_eq_constantCoeff_apply, hT, coeff_taylor]; simp [iterOp_zero]
  rw [zero_add, Nat.cast_one, one_le_order_iff_constCoeff_eq_zero, map_sub, h0]
  simp

theorem rel_coord (ev : A →+* R) (ds : Fin n → Derivation ℤ A A) (T : A →+* MvPowerSeries (Fin n) R)
    (hT : ∀ f, T f = taylor ev (fun i => ⇑(ds i)) f) (z : Fin n → A) (hz : ∀ i, ev (z i) = 0)
    (hd : ∀ a i, ev (ds a (z i)) = if a = i then 1 else 0) (i : Fin n) :
    Rel 1 (T (z i)) (X i) := by
  refine ⟨?_, ?_⟩
  · exact one_le_order_iff_constCoeff_eq_zero.2 (by simp)
  · refine nat_le_order fun d hd2 => ?_
    rw [map_sub, hT, coeff_taylor]
    by_cases h0 : d.degree = 0
    · rw [(Finsupp.degree_eq_zero_iff d).1 h0]; simp [iterOp_zero, hz]
    · obtain ⟨a, rfl⟩ := degree_eq_one (by omega : d.degree = 1)
      rw [iterOp_single, hd, coeff_X]
      have hf : ∀ j, (((Finsupp.single a 1 : Fin n →₀ ℕ) j).factorial : ℚ) = 1 := by
        intro j; rw [Finsupp.single_apply]; split_ifs <;> simp
      simp only [hf, Finset.prod_const_one, inv_one, one_smul]
      by_cases hai : a = i
      · subst hai; simp
      · simp [hai, Finsupp.single_left_inj (one_ne_zero)]

theorem step (ev : A →+* R) (ds : Fin n → Derivation ℤ A A) (T : A →+* MvPowerSeries (Fin n) R)
    (hT : ∀ f, T f = taylor ev (fun i => ⇑(ds i)) f) (z : Fin n → A) (hz : ∀ i, ev (z i) = 0)
    (hd : ∀ a i, ev (ds a (z i)) = if a = i then 1 else 0)
    (hker : RingHom.ker ev ≤ Ideal.span (Set.range z)) (k : ℕ) (f : A) (hf : T f = 0)
    (hk : f ∈ Ideal.span (Set.range z) ^ k) : f ∈ Ideal.span (Set.range z) ^ (k + 1) := by
  classical
  obtain ⟨p, hp, rfl⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous z f).1 hk
  have hdeg : ∀ β ∈ p.support, β.degree = k := by
    intro β hβ
    have := hp (MvPolynomial.mem_support_iff.1 hβ)
    rw [Finsupp.degree_eq_weight_one]; exact this
  have hev : MvPolynomial.eval z p = ∑ β ∈ p.support, p.coeff β * ∏ i, z i ^ β i :=
    MvPolynomial.eval_eq' z p
  have hmon : ∀ (β : Fin n →₀ ℕ) (c : R), C c * ∏ i, (X i : MvPowerSeries (Fin n) R) ^ β i = monomial β c := by
    intro β c
    simp only [X_pow_eq]
    rw [prod_monomial, ← monomial_zero_eq_C_apply, monomial_mul_monomial]
    simp [Finsupp.univ_sum_single]
  set G : MvPowerSeries (Fin n) R := ∑ β ∈ p.support, monomial β (ev (p.coeff β)) with hGdef
  have hrel : ∀ β ∈ p.support,
      Rel k (T (p.coeff β * ∏ i, z i ^ β i)) (monomial β (ev (p.coeff β))) := by
    intro β hβ
    have h := rel_mul (rel_const ev _ T hT (p.coeff β))
      (rel_prod_pow Finset.univ (fun i => T (z i)) X (fun i => β i) (rel_coord ev ds T hT z hz hd))
    rw [zero_add, ← Finsupp.degree_eq_sum, hdeg β hβ, hmon] at h
    rw [map_mul, map_prod]; simp only [map_pow]; exact h
  have hcoef : ∀ α : Fin n →₀ ℕ, α.degree = k →
      coeff α (T (MvPolynomial.eval z p)) = coeff α G := by
    intro α hα
    rw [← sub_eq_zero, ← map_sub, hev, map_sum, hGdef, ← Finset.sum_sub_distrib, map_sum]
    refine Finset.sum_eq_zero fun β hβ => coeff_of_lt_order ?_
    exact lt_of_lt_of_le (by rw [hα]; exact_mod_cast Nat.lt_succ_self k) (hrel β hβ).2
  have hG : ∀ α, coeff α G = ev (p.coeff α) := by
    intro α
    simp only [hGdef, map_sum, coeff_monomial, Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · rw [MvPolynomial.mem_support_iff, not_not] at h; rw [h, map_zero]
  rw [hev]
  refine Ideal.sum_mem _ fun β hβ => ?_
  rw [pow_succ']
  refine Ideal.mul_mem_mul (hker (RingHom.mem_ker.2 ?_)) ?_
  · rw [← hG, ← hcoef β (hdeg β hβ), hf, map_zero]
  · rw [← hdeg β hβ, Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _

end Main

theorem taylor_injective : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [Algebra ℚ R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (inc : R →+* A) (ev : A →+* R), (∀ r, ev (inc r) = r) → ∀ (n : ℕ) (ds : Fin n → Derivation ℤ A A) (z : Fin n → A), (∀ i, ev (z i) = 0) → (∀ a i, ev (ds a (z i)) = if a = i then 1 else 0) → maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z) → ∀ f, taylor ev (fun i => ⇑(ds i)) f = 0 → f = 0 := by
  intro R A _ _ _ _ _ _ inc ev hev n ds z hz hd hm f hf
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_ringHom_eq_taylor A R n ev ds
  have hker := ker_le_span inc ev hev z hz hm
  have hTf : T f = 0 := by rw [hT]; exact hf
  have hall : ∀ k, f ∈ Ideal.span (Set.range z) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => exact step ev ds T hT z hz hd hker k f hTf ih
  have hne : Ideal.span (Set.range z) ≠ ⊤ := by
    intro h
    apply (maximalIdeal.isMaximal A).ne_top
    rw [eq_top_iff, hm, ← h]; exact le_sup_right
  have := Ideal.iInf_pow_eq_bot_of_isLocalRing _ hne
  rw [← Ideal.mem_bot, ← this, Ideal.mem_iInf]; exact hall

end GlobalTheory.TaylorInj
