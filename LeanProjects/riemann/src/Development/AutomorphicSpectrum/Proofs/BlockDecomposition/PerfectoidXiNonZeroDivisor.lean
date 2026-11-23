import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.UntiltRegular

variable {W R : Type*} [CommRing W] [CommRing R]

theorem mem_span_of_mul_mem_of_hom {l xi : W} (φ : W →+* R)
    (hmem : ∀ y, y ∈ Ideal.span {l} ↔ φ y = 0) (hxi : φ xi ∈ nonZeroDivisors R) (y : W)
    (h : xi * y ∈ Ideal.span {l}) : y ∈ Ideal.span {l} := by
  rw [hmem] at h ⊢
  rw [map_mul] at h
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hxi).mp h

private theorem eq_zero_of_pow_mul_eq_zero_of_nonzerodivisor' {l : W} (hl : ∀ x, l * x = 0 → x = 0) (m : ℕ) :
    ∀ t : W, l ^ m * t = 0 → t = 0 := by
  induction m with
  | zero => intro t ht; simpa using ht
  | succ m ihm =>
    intro t ht
    rw [pow_succ, mul_assoc] at ht
    exact hl t (ihm _ ht)

theorem mem_span_pow_of_mul_mem {l xi : W} (hl : ∀ x, l * x = 0 → x = 0)
    (key : ∀ y, xi * y ∈ Ideal.span {l} → y ∈ Ideal.span {l}) (n : ℕ) :
    ∀ x, xi * x ∈ Ideal.span {l ^ n} → x ∈ Ideal.span {l ^ n} := by
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    have hx' : xi * x ∈ Ideal.span {l ^ n} := by
      rw [Ideal.mem_span_singleton] at hx ⊢
      exact (pow_dvd_pow l (Nat.le_succ n)).trans hx
    have h1 := ih x hx'
    rw [Ideal.mem_span_singleton] at h1 hx ⊢
    obtain ⟨c, rfl⟩ := h1
    obtain ⟨d, hd⟩ := hx
    have h2 : xi * c = l * d := by
      have h0 : l ^ n * (xi * c - l * d) = 0 := by linear_combination hd
      exact sub_eq_zero.mp (eq_zero_of_pow_mul_eq_zero_of_nonzerodivisor' hl n _ h0)
    obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton.mp (key c (Ideal.mem_span_singleton.mpr ⟨d, h2⟩))
    exact ⟨e, by ring⟩

theorem eq_zero_of_mul_eq_zero {l xi : W} (hl : ∀ x, l * x = 0 → x = 0)
    (hH : IsHausdorff (Ideal.span {l}) W)
    (key : ∀ y, xi * y ∈ Ideal.span {l} → y ∈ Ideal.span {l}) (y : W) (h : xi * y = 0) :
    y = 0 := by
  have hall : ∀ n, y ∈ Ideal.span {l ^ n} :=
    fun n => mem_span_pow_of_mul_mem hl key n y (by rw [h]; exact zero_mem _)
  apply hH.haus y
  intro n
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact hall n

theorem mem_span_xi_of_mul_mem {l xi : W} (hl : ∀ x, l * x = 0 → x = 0)
    (key : ∀ y, xi * y ∈ Ideal.span {l} → y ∈ Ideal.span {l}) (y : W)
    (h : l * y ∈ Ideal.span {xi}) : y ∈ Ideal.span {xi} := by
  rw [Ideal.mem_span_singleton] at h ⊢
  obtain ⟨c, hc⟩ := h
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp (key c (Ideal.mem_span_singleton.mpr ⟨y, hc.symm⟩))
  refine ⟨d, sub_eq_zero.mp (hl _ ?_)⟩
  linear_combination hc

theorem regular_of_key {l xi : W} (hl : ∀ x, l * x = 0 → x = 0)
    (hH : IsHausdorff (Ideal.span {l}) W)
    (key : ∀ y, xi * y ∈ Ideal.span {l} → y ∈ Ideal.span {l}) :
    Ideal.Quotient.mk (Ideal.span {xi}) l ∈ nonZeroDivisors (W ⧸ Ideal.span {xi}) ∧
      xi ∈ nonZeroDivisors W ∧
      ∀ (n : ℕ) (x : W), xi * x ∈ Ideal.span {l ^ n} → x ∈ Ideal.span {l ^ n} := by
  refine ⟨?_, ?_, mem_span_pow_of_mul_mem hl key⟩
  · rw [mem_nonZeroDivisors_iff]
    have hq : ∀ x : W ⧸ Ideal.span {xi}, x * Ideal.Quotient.mk (Ideal.span {xi}) l = 0 → x = 0 := by
      intro x hx
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hx
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact mem_span_xi_of_mul_mem hl key x (by rw [mul_comm]; exact hx)
    exact ⟨fun x hx => hq x (by rw [mul_comm]; exact hx), hq⟩
  · rw [mem_nonZeroDivisors_iff]
    have hw : ∀ x : W, xi * x = 0 → x = 0 := fun x hx => eq_zero_of_mul_eq_zero hl hH key x hx
    exact ⟨hw, fun x hx => hw x (by rw [mul_comm]; exact hx)⟩

theorem key {l : ℕ} [Fact l.Prime] (A : PAlg l) (y : A.W)
    (h : A.xi * y ∈ Ideal.span {(l : A.W)}) : y ∈ Ideal.span {(l : A.W)} := by
  refine mem_span_of_mul_mem_of_hom (WittVector.constantCoeff : A.W →+* A.A) (fun x => ?_) ?_ y h
  · rw [A.mem_span_l_iff x]
    exact Iff.rfl
  · have hc : (WittVector.constantCoeff : A.W →+* A.A) A.xi = -A.pi := A.xi_coeff_zero
    have hpi : A.pi ∈ nonZeroDivisors A.A := A.tf
    rw [hc, ← neg_one_mul]
    exact mul_mem isUnit_one.neg.mem_nonZeroDivisors hpi

theorem untilt_regular : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l),
    (l : A.U) ∈ nonZeroDivisors A.U ∧ A.xi ∈ nonZeroDivisors A.W ∧
      ∀ (n : ℕ) (x : A.W), A.xi * x ∈ Ideal.span {(l : A.W) ^ n} →
        x ∈ Ideal.span {(l : A.W) ^ n} := by
  intro l _ A
  have hreg := regular_of_key (W := A.W) (l := (l : A.W)) (xi := A.xi)
    (fun x hx => A.l_mul_eq_zero hx) inferInstance (fun y hy => key A y hy)
  refine ⟨?_, hreg.2.1, hreg.2.2⟩
  have h1 := hreg.1
  rw [map_natCast] at h1
  exact h1

end GlobalTheory.CompanionTheory.UntiltRegular
