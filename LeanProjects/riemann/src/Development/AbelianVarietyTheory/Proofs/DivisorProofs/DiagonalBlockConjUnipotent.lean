import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PutMulPut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PutLinPack
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul

section
variable {R : Type} [CommRing R] {n : ℕ}

private theorem comm_pm (o₁ o₂ o₃ : ℕ) {p q s : ℕ} (X : Matrix (Fin p) (Fin q) R) (Y : Matrix (Fin q) (Fin s) R)
    (h : o₂ + q ≤ n) : put n o₁ o₂ X * put n o₂ o₃ Y = put n o₁ o₃ (X * Y) :=
  (put_mul_put R n o₁ o₂ o₃ 0 p q s q X Y Y).1 h

private theorem comm_pz (o₁ o₂ o₃ o₄ : ℕ) {p q s t : ℕ} (X : Matrix (Fin p) (Fin q) R) (Z : Matrix (Fin t) (Fin s) R)
    (h : o₂ + q ≤ o₃ ∨ o₃ + t ≤ o₂) : put n o₁ o₂ X * put n o₃ o₄ Z = 0 :=
  (put_mul_put R n o₁ o₂ o₃ o₄ p q s t X 0 Z).2 h

private theorem comm_toGL (M N : Matrix (Fin n) (Fin n) R) (h₁ : M * N = 1) (h₂ : N * M = 1) : (toGL M).val = M := by
  have := toGL_val (⟨M, N, h₁, h₂⟩ : GL (Fin n) R)
  exact congrArg Units.val this

private theorem comm_uni {o₁ o₂ p q : ℕ} (X : Matrix (Fin p) (Fin q) R) (h : o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) :
    (uni n o₁ o₂ X).val = 1 + put n o₁ o₂ X := by
  have h0 : put n o₁ o₂ X * put n o₁ o₂ X = 0 := comm_pz _ _ _ _ _ _ h.symm
  refine comm_toGL _ (1 - put n o₁ o₂ X) ?_ ?_
  · simp only [add_mul, mul_sub, mul_one, one_mul, h0]; abel
  · simp only [mul_add, sub_mul, mul_one, one_mul, h0]; abel

private theorem comm_dgmul {o p : ℕ} (A B : Matrix (Fin p) (Fin p) R) (hAB : A * B = 1) (h : o + p ≤ n) :
    (1 - eye R n o o p + put n o o A) * (1 - eye R n o o p + put n o o B) = 1 := by
  simp only [eye, add_mul, mul_add, mul_sub, sub_mul, mul_one, one_mul, comm_pm _ _ _ _ _ h, hAB]
  abel

private theorem comm_dg {o p : ℕ} (g : GL (Fin p) R) (h : o + p ≤ n) :
    (dg n o g).val = 1 - eye R n o o p + put n o o g.val :=
  comm_toGL _ (1 - eye R n o o p + put n o o g⁻¹.val) (comm_dgmul _ _ g.mul_inv h) (comm_dgmul _ _ g.inv_mul h)

end

theorem dg_uni_comm : ∀ (R : Type) [CommRing R] (n o₁ o₂ p q : ℕ), (o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) → o₁ + p ≤ n → o₂ + q ≤ n → (∀ (g : GL (Fin p) R) (X : Matrix (Fin p) (Fin q) R), dg n o₁ g * uni n o₁ o₂ X = uni n o₁ o₂ (g.val * X) * dg n o₁ g) ∧ (∀ (g : GL (Fin q) R) (X : Matrix (Fin p) (Fin q) R), uni n o₁ o₂ X * dg n o₂ g = dg n o₂ g * uni n o₁ o₂ (X * g.val)) ∧ (∀ (a : GL (Fin p) R) (b : GL (Fin q) R), dg n o₁ a * dg n o₂ b = dg n o₂ b * dg n o₁ a) := by
  intro R _ n o₁ o₂ p q h h₁ h₂
  refine ⟨fun g X => Units.ext ?_, fun g X => Units.ext ?_, fun a b => Units.ext ?_⟩
  · simp only [Units.val_mul, comm_uni _ h, comm_dg _ h₁, eye, add_mul, mul_add, mul_sub, sub_mul, mul_one, one_mul,
      comm_pm _ _ _ _ _ h₁, comm_pz _ _ _ _ _ _ h.symm, Matrix.one_mul]
    abel
  · simp only [Units.val_mul, comm_uni _ h, comm_dg _ h₂, eye, add_mul, mul_add, mul_sub, sub_mul, mul_one, one_mul,
      comm_pm _ _ _ _ _ h₂, comm_pz _ _ _ _ _ _ h.symm, Matrix.mul_one]
    abel
  · simp only [Units.val_mul, comm_dg _ h₁, comm_dg _ h₂, eye, add_mul, mul_add, mul_sub, sub_mul, mul_one, one_mul,
      comm_pz _ _ _ _ _ _ h, comm_pz _ _ _ _ _ _ h.symm]
    abel

end GlobalTheory.GamMul
