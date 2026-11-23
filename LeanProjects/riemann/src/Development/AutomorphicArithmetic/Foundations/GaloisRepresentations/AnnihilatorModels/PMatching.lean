import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem descend (hS : SameNormBasic) {B ι : Type} [CommRing B] [Fintype ι] {a b : B} (hab : a ∣ b)
    {u u' : Multiset (ι → B)} (h : SameNorm (redMod b u) (redMod b u')) :
    SameNorm (redMod a u) (redMod a u') := by
  have hle : Ideal.span {b} ≤ Ideal.span {a} := Ideal.span_singleton_le_span_singleton.2 hab
  have := (hS (B ⧸ Ideal.span {b}) ι).1 (B ⧸ Ideal.span {a}) (Ideal.Quotient.factor hle) _ _ h
  simpa only [redMod, Multiset.map_map, Function.comp_def, Ideal.Quotient.factor_mk] using this

private theorem red_cons {B ι : Type} [CommRing B] (a : B) (x : ι → B) (u : Multiset (ι → B)) :
    redMod a (x ::ₘ u) = (fun k => Ideal.Quotient.mk (Ideal.span {a}) (x k)) ::ₘ redMod a u := by
  simp [redMod]

private theorem red_eq {B ι : Type} [CommRing B] {a : B} {x y : ι → B} (h : ∀ k, a ∣ x k - y k) :
    (fun k => Ideal.Quotient.mk (Ideal.span {a}) (x k)) = fun k => Ideal.Quotient.mk (Ideal.span {a}) (y k) := by
  funext k
  exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (h k))

private theorem main (hS : SameNormBasic) (hM : MatchStep) {B : Type} [CommRing B] (ϖ : B)
    (h0 : ϖ ∈ nonZeroDivisors B) (h1 : ¬ IsUnit ϖ) {ι : Type} [Fintype ι] (N : ℕ) :
    ∀ c, c ≤ N → ∀ (u u' : Multiset (ι → B)), u.card = c → u'.card ≤ N →
    (∀ x ∈ u, ∀ y ∈ u', ∀ k k', x k - y k ∣ ϖ ^ (N + 1) ^ N → x k - y k ∣ x k' - y k' ∨ x k' - y k' ∣ x k - y k) →
    (∀ x ∈ u, ∀ y ∈ u', ∀ k, ∀ j ≤ N, x k - y k ∣ ϖ ^ (N + 1) ^ j ∨ ϖ ^ (N + 1) ^ j ∣ x k - y k) →
    SameNorm (redMod (ϖ ^ (N + 1) ^ c) u) (redMod (ϖ ^ (N + 1) ^ c) u') →
    redMod ϖ u = redMod ϖ u' := by
  have hnu : ∀ j : ℕ, j ≠ 0 → ¬ IsUnit (ϖ ^ j) := fun j hj h => h1 ((isUnit_pow_iff hj).mp h)
  intro c
  induction c with
  | zero =>
    intro _ u u' hu _ _ _ hsn
    have hu0 : u = 0 := Multiset.card_eq_zero.mp hu
    subst hu0
    haveI : Nontrivial (B ⧸ Ideal.span {ϖ ^ (N + 1) ^ 0}) := by
      refine nontrivial_of_ne 1 0 ?_
      intro h
      rw [← map_one (Ideal.Quotient.mk (Ideal.span {ϖ ^ (N + 1) ^ 0})),
        Ideal.Quotient.eq_zero_iff_mem, ← Ideal.eq_top_iff_one, Ideal.span_singleton_eq_top] at h
      exact hnu _ (by positivity) h
    have hc := (hS _ ι).2.2.1 inferInstance _ _ hsn
    have hu'0 : u' = 0 := by
      simp only [redMod, Multiset.card_map, Multiset.card_zero, Multiset.map_zero] at hc
      exact Multiset.card_eq_zero.mp hc.symm
    subst hu'0
    rfl
  | succ c ih =>
    intro hc u u' hu hu' hdiv hcmp hsn
    obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp (by rw [hu]; exact Nat.succ_pos c)
    obtain ⟨u0, rfl⟩ := Multiset.exists_cons_of_mem hx
    have hxm : x ∈ x ::ₘ u0 := Multiset.mem_cons.mpr (Or.inl rfl)
    have hm : 0 < (N + 1) ^ c := by positivity
    have hle : (N + 1) ^ c ≤ (N + 1) ^ N := Nat.pow_le_pow_right (Nat.succ_pos N) (by omega)
    have hsn' : SameNorm (redMod (ϖ ^ ((N + 1) ^ c * (N + 1))) (x ::ₘ u0))
        (redMod (ϖ ^ ((N + 1) ^ c * (N + 1))) u') := by
      rw [← pow_succ]; exact hsn
    obtain ⟨y, hy, hxy⟩ := hM B ϖ h0 h1 ι N ((N + 1) ^ c) hm (x ::ₘ u0) u' hu' hsn' x hxm
      (fun y hy k k' h => hdiv x hxm y hy k k' (h.trans (pow_dvd_pow ϖ hle)))
      (fun y hy k => hcmp x hxm y hy k c (by omega))
    obtain ⟨u0', rfl⟩ := Multiset.exists_cons_of_mem hy
    have hsn2 : SameNorm (redMod (ϖ ^ (N + 1) ^ c) (x ::ₘ u0)) (redMod (ϖ ^ (N + 1) ^ c) (y ::ₘ u0')) :=
      descend hS (pow_dvd_pow ϖ (Nat.pow_le_pow_right (Nat.succ_pos N) (Nat.le_succ c))) hsn
    rw [red_cons, red_cons, red_eq hxy] at hsn2
    have hsn3 := (hS _ ι).2.1 _ _ _ hsn2
    have ih' := ih (by omega) u0 u0' (by simpa using hu) (by simp at hu'; omega)
      (fun a ha b hb => hdiv a (Multiset.mem_cons_of_mem ha) b (Multiset.mem_cons_of_mem hb))
      (fun a ha b hb => hcmp a (Multiset.mem_cons_of_mem ha) b (Multiset.mem_cons_of_mem hb)) hsn3
    rw [red_cons, red_cons, ih', red_eq (fun k => (dvd_pow_self ϖ hm.ne').trans (hxy k))]

theorem UpperTheory.Gal.crystallineComparison.matching_of :
    SameNormBasic → MatchStep → Matching := by
  intro hS hM B _ ϖ h0 h1 ι _ N u u' hu hu' hsn hdiv hcmp
  apply main hS hM ϖ h0 h1 N u.card hu u u' rfl hu' hdiv hcmp
  exact descend hS (pow_dvd_pow _ (Nat.pow_le_pow_right (Nat.succ_pos N) hu)) hsn
