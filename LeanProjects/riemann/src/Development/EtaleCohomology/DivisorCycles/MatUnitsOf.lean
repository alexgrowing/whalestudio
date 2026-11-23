import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix

namespace LateralTheory.DivDb.MatrixUnitConstruction
open LateralTheory.DivDb

variable {C : Type} [Field C] {N n : ℕ}

def Pr (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N) (i j : Fin n) (x y : Mat C N) : Prop :=
  x ∈ A ∧ y ∈ A ∧ p i * x * p j = x ∧ p j * y * p i = y ∧ x * y = p i ∧ y * x = p j

def rel (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N) (i j : Fin n) : Prop := ∃ x y, Pr A p i j x y

section
variable {A : Subalgebra C (Mat C N)} {p : Fin n → Mat C N}

lemma idem (hp : Sys p) (i : Fin n) : p i * p i = p i := (hp.1.idem i).eq

lemma idemL (hp : Sys p) (i : Fin n) (X : Mat C N) : p i * (p i * X) = p i * X := by
  rw [← mul_assoc, idem hp i]

lemma sand_left (hp : Sys p) {i j : Fin n} {x : Mat C N} (h : p i * x * p j = x) : p i * x = x := by
  conv_lhs => rw [← h]
  simp only [mul_assoc, idemL hp i]
  simpa only [mul_assoc] using h

lemma sand_right (hp : Sys p) {i j : Fin n} {x : Mat C N} (h : p i * x * p j = x) : x * p j = x := by
  conv_lhs => rw [← h]
  rw [mul_assoc (p i * x), idem hp j, h]

lemma pr_ne (hp : Sys p) {i j : Fin n} {x y : Mat C N} (h : Pr A p i j x y) : x ≠ 0 := by
  rintro rfl
  exact hp.2 i (by rw [← h.2.2.2.2.1, zero_mul])

lemma pr_symm {i j : Fin n} {x y : Mat C N} (h : Pr A p i j x y) : Pr A p j i y x :=
  ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.2, h.2.2.2.2.1⟩

lemma pr_refl (hp : Sys p) (hc : Corner A p) (i : Fin n) : Pr A p i i (p i) (p i) :=
  ⟨hc.1 i, hc.1 i, by rw [idem hp i, idem hp i], by rw [idem hp i, idem hp i], idem hp i, idem hp i⟩

lemma pr_trans (hp : Sys p) {i j k : Fin n} {x y x' y' : Mat C N} (h : Pr A p i j x y)
    (h' : Pr A p j k x' y') : Pr A p i k (x * x') (y' * y) := by
  refine ⟨A.mul_mem h.1 h'.1, A.mul_mem h'.2.1 h.2.1, ?_, ?_, ?_, ?_⟩
  · rw [← mul_assoc, sand_left hp h.2.2.1, mul_assoc, sand_right hp h'.2.2.1]
  · rw [← mul_assoc, sand_left hp h'.2.2.2.1, mul_assoc, sand_right hp h.2.2.2.1]
  · rw [show x * x' * (y' * y) = x * (x' * y') * y by simp only [mul_assoc], h'.2.2.2.2.1,
      sand_right hp h.2.2.1, h.2.2.2.2.1]
  · rw [show y' * y * (x * x') = y' * (y * x) * x' by simp only [mul_assoc], h.2.2.2.2.2,
      sand_right hp h'.2.2.2.1, h'.2.2.2.2.2]

lemma partner (hp : Sys p) (hc : Corner A p) (hA : NoNil A) {i j : Fin n} {Y : Mat C N}
    (hYA : Y ∈ A) (hYl : p i * Y = Y) (hYr : Y * p j = Y) (hY0 : Y ≠ 0) :
    ∃ w, Pr A p i j Y w := by
  obtain ⟨b, hb, hnil⟩ : ∃ b ∈ A, ¬ IsNilpotent (b * Y) := by
    by_contra h
    push Not at h
    exact hY0 (hA Y hYA h)
  have hwA : p j * b * p i ∈ A := A.mul_mem (A.mul_mem (hc.1 j) hb) (hc.1 i)
  obtain ⟨c, hc1⟩ := hc.2 (Y * b) (A.mul_mem hYA hb) i
  obtain ⟨d, hd1⟩ := hc.2 (b * Y) (A.mul_mem hb hYA) j
  have hYw : Y * (p j * b * p i) = c • p i := by
    rw [← hc1]
    calc Y * (p j * b * p i) = (Y * p j) * b * p i := by simp only [mul_assoc]
      _ = (p i * Y) * b * p i := by rw [hYr, hYl]
      _ = p i * (Y * b) * p i := by simp only [mul_assoc]
  have hwY : (p j * b * p i) * Y = d • p j := by
    rw [← hd1]
    calc p j * b * p i * Y = p j * b * (p i * Y) := by simp only [mul_assoc]
      _ = p j * b * (Y * p j) := by rw [hYl, hYr]
      _ = p j * (b * Y) * p j := by simp only [mul_assoc]
  have e1 : Y * (p j * b * p i) * Y = c • Y := by rw [hYw, smul_mul_assoc, hYl]
  have e2 : Y * (p j * b * p i) * Y = d • Y := by rw [mul_assoc, hwY, mul_smul_comm, hYr]
  have hcd : c = d := by
    by_contra h
    have h3 : (c - d) • Y = 0 := by rw [sub_smul, ← e1, ← e2, sub_self]
    exact hY0 ((smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr h))
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hnil
    refine ⟨2, ?_⟩
    have h0 : Y * b * Y = 0 := by
      have : Y * b * Y = Y * (p j * b * p i) * Y := by
        rw [show Y * (p j * b * p i) * Y = (Y * p j) * b * (p i * Y) by simp only [mul_assoc], hYr, hYl]
      rw [this, e1, zero_smul]
    rw [pow_two, show b * Y * (b * Y) = b * (Y * b * Y) by simp only [mul_assoc], h0, mul_zero]
  refine ⟨c⁻¹ • (p j * b * p i), hYA, A.smul_mem hwA _, ?_, ?_, ?_, ?_⟩
  · rw [hYl, hYr]
  · rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    simp only [mul_assoc, idem hp i, idemL hp j]
  · rw [mul_smul_comm, hYw, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  · rw [smul_mul_assoc, hwY, ← hcd, smul_smul, inv_mul_cancel₀ hc0, one_smul]

lemma oneDim (hp : Sys p) (hc : Corner A p) {i j : Fin n} {x y : Mat C N} (h : Pr A p i j x y)
    {a : Mat C N} (ha : a ∈ A) : ∃ c : C, p i * a * p j = c • x := by
  obtain ⟨c, hc1⟩ := hc.2 (a * p j * y) (A.mul_mem (A.mul_mem ha (hc.1 j)) h.2.1) i
  refine ⟨c, ?_⟩
  have hy : y * p i = y := sand_right hp h.2.2.2.1
  have h1 : p i * a * p j * y = c • p i := by
    calc p i * a * p j * y = p i * a * p j * (y * p i) := by rw [hy]
      _ = p i * (a * p j * y) * p i := by simp only [mul_assoc]
      _ = c • p i := hc1
  calc p i * a * p j = p i * a * p j * p j := by rw [mul_assoc (p i * a) (p j) (p j), idem hp j]
    _ = p i * a * p j * (y * x) := by rw [h.2.2.2.2.2]
    _ = (p i * a * p j * y) * x := by simp only [mul_assoc]
    _ = c • x := by rw [h1, smul_mul_assoc, sand_left hp h.2.2.1]

lemma rel_equiv (hp : Sys p) (hc : Corner A p) : Equivalence (rel A p) where
  refl i := ⟨_, _, pr_refl hp hc i⟩
  symm := fun ⟨_, _, h⟩ => ⟨_, _, pr_symm h⟩
  trans := fun ⟨_, _, h⟩ ⟨_, _, h'⟩ => ⟨_, _, pr_trans hp h h'⟩

end

open Classical in
theorem MatUnits_of : MatrixUnits₂ := by
  intro C _ N n A p hp hc hA
  have heq := rel_equiv hp hc
  let s : Setoid (Fin n) := ⟨rel A p, heq⟩
  obtain ⟨r, hr, hreq⟩ : ∃ r : Fin n → Fin n, (∀ i, ∃ x y, Pr A p i (r i) x y) ∧
      ∀ i j, rel A p i j → r i = r j :=
    ⟨fun i => (Quotient.mk s i).out, fun i => heq.symm (Quotient.mk_out (s := s) i),
      fun i j h => congrArg Quotient.out (Quotient.sound (s := s) h)⟩
  choose X Y hXY using hr
  have pairE : ∀ i j, rel A p i j → Pr A p i j (X i * Y j) (X j * Y i) := by
    intro i j h
    have h2 := hXY j
    rw [← hreq i j h] at h2
    exact pr_trans hp (hXY i) (pr_symm h2)
  refine ⟨fun i j => if rel A p i j then X i * Y j else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases h : rel A p i j
    · simp only [if_pos h]; exact (pairE i j h).1
    · simp only [if_neg h]; exact A.zero_mem
  · intro i
    simp only [if_pos (heq.refl i)]
    exact (hXY i).2.2.2.2.1
  · intro i j
    by_cases h : rel A p i j
    · simp only [if_pos h]; exact (pairE i j h).2.2.1
    · simp only [if_neg h, mul_zero, zero_mul]
  · intro i j hne
    have h : rel A p i j := by
      by_contra h
      simp only [if_neg h] at hne
      exact hne rfl
    simp only [if_pos (heq.symm h)]
    exact pr_ne hp (pairE j i (heq.symm h))
  · intro i j k h1 h2
    have hij : rel A p i j := by
      by_contra h
      simp only [if_neg h] at h1
      exact h1 rfl
    have hjk : rel A p j k := by
      by_contra h
      simp only [if_neg h] at h2
      exact h2 rfl
    have hik := heq.trans hij hjk
    simp only [if_pos hij, if_pos hjk, if_pos hik]
    refine ⟨?_, pr_ne hp (pairE i k hik)⟩
    rw [show X i * Y j * (X j * Y k) = X i * (Y j * X j) * Y k by simp only [mul_assoc],
      (hXY j).2.2.2.2.2, ← hreq i j hij, sand_right hp (hXY i).2.2.1]
  · intro a ha i j
    by_cases h : rel A p i j
    · simp only [if_pos h]; exact oneDim hp hc (pairE i j h) ha
    · refine ⟨0, ?_⟩
      simp only [if_neg h, smul_zero]
      by_contra h'
      obtain ⟨w, hw⟩ := partner (i := i) (j := j) hp hc hA (A.mul_mem (A.mul_mem (hc.1 i) ha) (hc.1 j))
        (by simp only [mul_assoc, idemL hp i]) (by rw [mul_assoc _ (p j), idem hp j]) h'
      exact h ⟨_, _, hw⟩

end LateralTheory.DivDb.MatrixUnitConstruction
