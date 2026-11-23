import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
open Ideal WittVector

namespace GlobalTheory

theorem isSMulRegular_natCast_adicCompletion (p : ℕ) (A : Type) [CommRing A]
    (hp : IsSMulRegular A (p : A)) :
    IsSMulRegular (AdicCompletion (Ideal.span {(p : A)}) A)
      (p : AdicCompletion (Ideal.span {(p : A)}) A) := by
  set I : Ideal A := Ideal.span {(p : A)}
  intro x y hxy
  have key : ∀ z : AdicCompletion I A, (p : AdicCompletion I A) * z = 0 → z = 0 := by
    intro z hz
    apply AdicCompletion.ext
    intro n
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (z.val (n + 1))
    have hz' : (p • z).val (n + 1) = 0 := by
      rw [nsmul_eq_mul, hz]; rfl
    rw [AdicCompletion.val_smul_apply, ← ha, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at hz'
    have hmem : (p : A) * a ∈ Ideal.span {(p : A) ^ (n + 1)} := by
      have : p • a = (p : A) * a := by rw [nsmul_eq_mul]
      rw [← this, ← Ideal.span_singleton_pow]
      simpa [smul_eq_mul, Ideal.mul_top] using hz'
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
    have hab : a = (p : A) ^ n * b := by
      apply hp
      simp only [smul_eq_mul]
      rw [← hb]; ring
    have htr := z.property (Nat.le_succ n)
    change AdicCompletion.transitionMap I A (Nat.le_succ n) (z.val (n + 1)) = z.val n at htr
    rw [← htr, ← ha, AdicCompletion.val_zero_apply]
    change (Submodule.Quotient.mk a : A ⧸ (I ^ n • ⊤ : Submodule A A)) = 0
    rw [Submodule.Quotient.mk_eq_zero, hab]
    simp only [smul_eq_mul, Ideal.mul_top, I, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton'.mpr ⟨b, mul_comm _ _⟩
  have h0 : (p : AdicCompletion I A) * (x - y) = 0 := by
    rw [mul_sub, sub_eq_zero]; exact hxy
  exact sub_eq_zero.mp (key _ h0)

end GlobalTheory
