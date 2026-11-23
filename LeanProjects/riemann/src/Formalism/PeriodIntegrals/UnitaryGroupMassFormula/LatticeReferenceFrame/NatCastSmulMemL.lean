import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.PPAssemble

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain

namespace PI.ScRefExists.PPA

open PI.ScRefExists.Sk

variable (I : Formalism.MainNotions.S.AutInst)

theorem hG_add_left (x x' y : Fin I.n → I.E) : hG I (x + x') y = hG I x y + hG I x' y := by
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem hG_add_right (x y y' : Fin I.n → I.E) : hG I x (y + y') = hG I x y + hG I x y' := by
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hG_smul_left (c : I.E) (x y : Fin I.n → I.E) : hG I (c • x) y = star c * hG I x y := by
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hG_smul_right (c : I.E) (x y : Fin I.n → I.E) : hG I x (c • y) = c * hG I x y := by
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hG_neg_left (x y : Fin I.n → I.E) : hG I (-x) y = -hG I x y := by
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, Pi.neg_apply, star_neg, neg_mul, Finset.sum_neg_distrib]

theorem hG_neg_right (x y : Fin I.n → I.E) : hG I x (-y) = -hG I x y := by
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem hG_sub_left (x x' y : Fin I.n → I.E) : hG I (x - x') y = hG I x y - hG I x' y := by
  rw [sub_eq_add_neg, hG_add_left, hG_neg_left, ← sub_eq_add_neg]

theorem hG_sub_right (x y y' : Fin I.n → I.E) : hG I x (y - y') = hG I x y - hG I x y' := by
  rw [sub_eq_add_neg, hG_add_right, hG_neg_right, ← sub_eq_add_neg]

theorem hG_symm (x y : Fin I.n → I.E) : hG I y x = star (hG I x y) := by
  have hJ : ∀ a b, star (I.J b a) = I.J a b := by
    intro a b
    have h : Formalism.UG.cT (starRingEnd I.E) I.J = I.J := I.J_herm
    have h2 := congrFun (congrFun h a) b
    simpa [Formalism.UG.cT, starRingEnd_apply] using h2
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, star_sum, star_mul', star_star]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hJ a b]
  ring

private theorem mem_Ap_lemma (p : ℕ) (x : I.E) :
    x ∈ Ap I p ↔ ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * x = (a : I.E) :=
  Iff.rfl

theorem int_mem_Ap (p : ℕ) (a : 𝓞 I.E) : (a : I.E) ∈ Ap I p := (mem_Ap_lemma I p _).mpr ⟨1, Nat.coprime_one_left p, a, by simp⟩

theorem inv_mem_Ap (p s : ℕ) (hs : Nat.Coprime s p) : (s : I.E)⁻¹ ∈ Ap I p := by
  by_cases h0 : s = 0
  · subst h0
    simp
  · have hs0 : (s : I.E) ≠ 0 := Nat.cast_ne_zero.mpr h0
    exact (mem_Ap_lemma I p _).mpr ⟨s, hs, 1, by rw [mul_inv_cancel₀ hs0]; simp⟩

theorem natCast_smul_mem_L (s : ℕ) {x : Fin I.n → I.E} (hx : x ∈ I.L) : (s : I.E) • x ∈ I.L := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hx s

theorem oE_smul (a : 𝓞 I.E) (x : Fin I.n → I.E) : a • x = (a : I.E) • x := by
  ext i; simp [Algebra.smul_def]

theorem natE_smul (t : ℕ) (x : Fin I.n → I.E) : (t : I.E) • x = (t : 𝓞 I.E) • x := by
  rw [oE_smul]
  simp

theorem intE_smul_mem_L (a : 𝓞 I.E) {x : Fin I.n → I.E} (hx : x ∈ I.L) : (a : I.E) • x ∈ I.L := by
  rw [← oE_smul]
  exact I.L.smul_mem a hx

theorem LA_clear (p : ℕ) {v : Fin I.n → I.E} (hv : v ∈ LA I p) :
    ∃ s : ℕ, Nat.Coprime s p ∧ (s : I.E) • v ∈ I.L := by
  have hv' : v ∈ Submodule.span (Ap I p) (I.L : Set (Fin I.n → I.E)) := hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.coprime_one_left p, by simpa using hx⟩
  | zero => exact ⟨1, Nat.coprime_one_left p, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, Nat.Coprime.mul hs ht, ?_⟩
    have e : ((s * t : ℕ) : I.E) • (x + y) = (t : I.E) • ((s : I.E) • x) + (s : I.E) • ((t : I.E) • y) := by
      simp only [Nat.cast_mul, smul_add, smul_smul, mul_comm (t : I.E) (s : I.E)]
    rw [e]
    exact add_mem (natCast_smul_mem_L I t hsx) (natCast_smul_mem_L I s hty)
  | smul c x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨s0, hs0, a, ha⟩ := (mem_Ap_lemma I p (c : I.E)).mp c.2
    refine ⟨s0 * s, Nat.Coprime.mul hs0 hs, ?_⟩
    have hc : c • x = (c : I.E) • x := rfl
    have e : ((s0 * s : ℕ) : I.E) • (c • x) = (a : I.E) • ((s : I.E) • x) := by
      rw [hc, smul_smul, smul_smul, ← ha]
      push_cast
      congr 1
      ring
    rw [e]
    exact intE_smul_mem_L I a hsx

theorem hG_mem_Ap (p : ℕ) {v v' : Fin I.n → I.E} (hv : v ∈ LA I p) (hv' : v' ∈ LA I p) :
    hG I v v' ∈ Ap I p := by
  obtain ⟨s, hs, hsv⟩ := LA_clear I p hv
  obtain ⟨t, ht, htv⟩ := LA_clear I p hv'
  obtain ⟨a, ha⟩ := RingHom.mem_range.mp ((I.L_dual _).mp htv _ hsv)
  have e : hG I ((s : I.E) • v) ((t : I.E) • v') = (s : I.E) * t * hG I v v' := by
    rw [hG_smul_left, hG_smul_right, star_natCast]
    ring
  refine (mem_Ap_lemma I p _).mpr ⟨s * t, Nat.Coprime.mul hs ht, a, ?_⟩
  rw [Nat.cast_mul, ← e]
  exact ha.symm

theorem span_clear (p : ℕ) (S : Set (Fin I.n → I.E)) {y : Fin I.n → I.E}
    (hy : y ∈ Submodule.span (Ap I p) S) :
    ∃ s : ℕ, Nat.Coprime s p ∧ (s : I.E) • y ∈ Submodule.span (𝓞 I.E) S := by
  have key : ∀ (a : 𝓞 I.E) {z : Fin I.n → I.E}, z ∈ Submodule.span (𝓞 I.E) S →
      (a : I.E) • z ∈ Submodule.span (𝓞 I.E) S := fun a z hz => by
    rw [← oE_smul]
    exact Submodule.smul_mem _ a hz
  have keyN : ∀ (t : ℕ) {z : Fin I.n → I.E}, z ∈ Submodule.span (𝓞 I.E) S →
      (t : I.E) • z ∈ Submodule.span (𝓞 I.E) S := fun t z hz => by
    rw [natE_smul]
    exact Submodule.smul_mem _ _ hz
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.coprime_one_left p, by simpa using Submodule.subset_span hx⟩
  | zero => exact ⟨1, Nat.coprime_one_left p, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, Nat.Coprime.mul hs ht, ?_⟩
    have e : ((s * t : ℕ) : I.E) • (x + y) = (t : I.E) • ((s : I.E) • x) + (s : I.E) • ((t : I.E) • y) := by
      simp only [Nat.cast_mul, smul_add, smul_smul, mul_comm (t : I.E) (s : I.E)]
    rw [e]
    exact add_mem (keyN t hsx) (keyN s hty)
  | smul c x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨s0, hs0, a, ha⟩ := (mem_Ap_lemma I p (c : I.E)).mp c.2
    refine ⟨s0 * s, Nat.Coprime.mul hs0 hs, ?_⟩
    have hc : c • x = (c : I.E) • x := rfl
    have e : ((s0 * s : ℕ) : I.E) • (c • x) = (a : I.E) • ((s : I.E) • x) := by
      rw [hc, smul_smul, smul_smul, ← ha]
      push_cast
      congr 1
      ring
    rw [e]
    exact key a hsx

def QA (p q : ℕ) (x : I.E) : Prop := ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * x = (q : I.E) * a

theorem QA_of_GE (p q : ℕ) {x : I.E} (h : GE I q x) : QA I p q x := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨1, Nat.coprime_one_left p, t, by simp⟩

theorem QA_add (p q : ℕ) {x y : I.E} (hx : QA I p q x) (hy : QA I p q y) : QA I p q (x + y) := by
  obtain ⟨s, hs, a, ha⟩ := hx
  obtain ⟨t, ht, b, hb⟩ := hy
  refine ⟨s * t, Nat.Coprime.mul hs ht, (t : 𝓞 I.E) * a + (s : 𝓞 I.E) * b, ?_⟩
  push_cast at ha hb ⊢
  linear_combination (t : I.E) * ha + (s : I.E) * hb

theorem QA_neg (p q : ℕ) {x : I.E} (hx : QA I p q x) : QA I p q (-x) := by
  obtain ⟨s, hs, a, ha⟩ := hx
  refine ⟨s, hs, -a, ?_⟩
  push_cast
  linear_combination -ha

theorem QA_sub (p q : ℕ) {x y : I.E} (hx : QA I p q x) (hy : QA I p q y) : QA I p q (x - y) := by
  rw [sub_eq_add_neg]
  exact QA_add I p q hx (QA_neg I p q hy)

theorem QA_mul (p q : ℕ) {c x : I.E} (hc : c ∈ Ap I p) (hx : QA I p q x) : QA I p q (c * x) := by
  obtain ⟨s, hs, a, ha⟩ := hx
  obtain ⟨s0, hs0, a0, ha0⟩ := (mem_Ap_lemma I p c).mp hc
  refine ⟨s0 * s, Nat.Coprime.mul hs0 hs, a0 * a, ?_⟩
  push_cast
  linear_combination ((s : I.E) * x) * ha0 + (a0 : I.E) * ha

theorem QA_zero (p q : ℕ) : QA I p q 0 := ⟨1, Nat.coprime_one_left p, 0, by simp⟩

theorem GE_of_QA (p m : ℕ) {x : I.E} (hint : ∃ a : 𝓞 I.E, (a : I.E) = x) (h : QA I p (p ^ m) x) :
    GE I (p ^ m) x := by
  obtain ⟨b, rfl⟩ := hint
  obtain ⟨s, hs, a, ha⟩ := h
  have hcop : Nat.Coprime s (p ^ m) := Nat.Coprime.pow_right m hs
  have hz : (s : ℤ) * Nat.gcdA s (p ^ m) + ((p ^ m : ℕ) : ℤ) * Nat.gcdB s (p ^ m) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hcop]
    norm_num
  have hzE := congrArg (Int.cast : ℤ → I.E) hz
  push_cast at hzE ha
  refine ⟨(Nat.gcdA s (p ^ m) : 𝓞 I.E) * a + (Nat.gcdB s (p ^ m) : 𝓞 I.E) * b, ?_⟩
  have hA : (((Nat.gcdA s (p ^ m) : ℤ) : 𝓞 I.E) : I.E) = ((Nat.gcdA s (p ^ m) : ℤ) : I.E) :=
    map_intCast (algebraMap (𝓞 I.E) I.E) _
  have hB : (((Nat.gcdB s (p ^ m) : ℤ) : 𝓞 I.E) : I.E) = ((Nat.gcdB s (p ^ m) : ℤ) : I.E) :=
    map_intCast (algebraMap (𝓞 I.E) I.E) _
  push_cast
  linear_combination ((Nat.gcdA s (p ^ m) : ℤ) : I.E) * ha - (b : I.E) * hzE -
    (p : I.E) ^ m * (a : I.E) * hA - (b : I.E) * (p : I.E) ^ m * hB

end PI.ScRefExists.PPA
