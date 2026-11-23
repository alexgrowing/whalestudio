import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PutMulPut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PutLinPack
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul

theorem toGL_of_inv {R : Type} [CommRing R] {n : ℕ} (M N : Matrix (Fin n) (Fin n) R) (h₁ : M * N = 1)
    (h₂ : N * M = 1) : toGL M = ⟨M, N, h₁, h₂⟩ := by
  unfold toGL
  have hu : IsUnit M := ⟨⟨M, N, h₁, h₂⟩, rfl⟩
  rw [dif_pos hu]
  exact Units.ext rfl

theorem eye_mul_eye {R : Type} [CommRing R] (n o₁ o₂ o₃ b : ℕ) (h : o₂ + b ≤ n) :
    eye R n o₁ o₂ b * eye R n o₂ o₃ b = eye R n o₁ o₃ b := by
  unfold eye
  rw [(put_mul_put R n o₁ o₂ o₃ 0 b b b b (1 : Matrix (Fin b) (Fin b) R) 1 1).1 h, Matrix.mul_one]

theorem eye_mul_eye_zero {R : Type} [CommRing R] (n o₁ o₂ o₃ o₄ b c : ℕ) (h : o₂ + b ≤ o₃ ∨ o₃ + c ≤ o₂) :
    eye R n o₁ o₂ b * eye R n o₃ o₄ c = 0 := by
  unfold eye
  exact (put_mul_put R n o₁ o₂ o₃ o₄ b b c c (1 : Matrix (Fin b) (Fin b) R) 0 1).2 h

theorem val_uni_dg_shuf : ∀ (R : Type) [CommRing R] (n o₁ o₂ p q : ℕ),
    (∀ X : Matrix (Fin p) (Fin q) R, (o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) →
      (uni n o₁ o₂ X).val = 1 + put n o₁ o₂ X ∧ (uni n o₁ o₂ X)⁻¹.val = 1 - put n o₁ o₂ X) ∧
    (∀ g : GL (Fin p) R, o₁ + p ≤ n →
      (dg n o₁ g).val = 1 - eye R n o₁ o₁ p + put n o₁ o₁ g.val ∧
      (dg n o₁ g)⁻¹.val = 1 - eye R n o₁ o₁ p + put n o₁ o₁ g⁻¹.val) ∧
    (p ≤ n → (shuf R n p).val = eye R n 0 p (n - p) + eye R n (n - p) 0 p ∧
      (shuf R n p)⁻¹.val = eye R n p 0 (n - p) + eye R n 0 (n - p) p) := by
  intro R _ n o₁ o₂ p q
  refine ⟨?_, ?_, ?_⟩
  · intro X hX
    have hPP : put n o₁ o₂ X * put n o₁ o₂ X = 0 :=
      (put_mul_put R n o₁ o₂ o₁ o₂ p q q p X 0 X).2 hX.symm
    have h₁ : (1 + put n o₁ o₂ X) * (1 - put n o₁ o₂ X) = 1 := by
      rw [add_mul, one_mul, mul_sub, mul_one, hPP]; abel
    have h₂ : (1 - put n o₁ o₂ X) * (1 + put n o₁ o₂ X) = 1 := by
      rw [sub_mul, one_mul, mul_add, mul_one, hPP]; abel
    have e : uni n o₁ o₂ X = ⟨_, _, h₁, h₂⟩ := toGL_of_inv _ _ h₁ h₂
    rw [e]; exact ⟨rfl, rfl⟩
  · intro g hg
    have hm : ∀ A B : Matrix (Fin p) (Fin p) R, put n o₁ o₁ A * put n o₁ o₁ B = put n o₁ o₁ (A * B) :=
      fun A B => (put_mul_put R n o₁ o₁ o₁ o₁ p p p p A B B).1 hg
    have key : ∀ a b : GL (Fin p) R, a * b = 1 →
        (1 - eye R n o₁ o₁ p + put n o₁ o₁ a.val) * (1 - eye R n o₁ o₁ p + put n o₁ o₁ b.val) = 1 := by
      intro a b hab
      have hab' : a.val * b.val = 1 := by rw [← Units.val_mul, hab]; rfl
      simp only [eye, sub_mul, add_mul, mul_sub, mul_add, one_mul, mul_one, hm, Matrix.one_mul, Matrix.mul_one, hab']
      abel
    have h₁ := key g g⁻¹ (mul_inv_cancel g)
    have h₂ := key g⁻¹ g (inv_mul_cancel g)
    have e : dg n o₁ g = ⟨_, _, h₁, h₂⟩ := toGL_of_inv _ _ h₁ h₂
    rw [e]; exact ⟨rfl, rfl⟩
  · intro hp
    have hpk := (put_lin_pack R n 0 0 (n - p) p).2.2.2.2.1
    have hpk' := (put_lin_pack R n 0 0 p (n - p)).2.2.2.2.1
    have hone := (put_lin_pack R n 0 0 0 0).2.2.2.2.2.1
    have hs : n - p + p = n := Nat.sub_add_cancel hp
    have hs' : p + (n - p) = n := by omega
    rw [hs, hone, zero_add] at hpk
    rw [hs', hone, zero_add] at hpk'
    have h₁ : (eye R n 0 p (n - p) + eye R n (n - p) 0 p) * (eye R n p 0 (n - p) + eye R n 0 (n - p) p) = 1 := by
      rw [add_mul, mul_add, mul_add, eye_mul_eye n 0 p 0 (n - p) (by omega),
        eye_mul_eye_zero n 0 p 0 (n - p) (n - p) p (Or.inr (by omega)),
        eye_mul_eye_zero n (n - p) 0 p 0 p (n - p) (Or.inl (by omega)),
        eye_mul_eye n (n - p) 0 (n - p) p (by omega), hpk]
      abel
    have h₂ : (eye R n p 0 (n - p) + eye R n 0 (n - p) p) * (eye R n 0 p (n - p) + eye R n (n - p) 0 p) = 1 := by
      rw [add_mul, mul_add, mul_add, eye_mul_eye n p 0 p (n - p) (by omega),
        eye_mul_eye_zero n p 0 (n - p) 0 (n - p) p (Or.inl (by omega)),
        eye_mul_eye_zero n 0 (n - p) 0 p p (n - p) (Or.inr (by omega)),
        eye_mul_eye n 0 (n - p) 0 p (by omega), hpk']
      abel
    have e : shuf R n p = ⟨_, _, h₁, h₂⟩ := toGL_of_inv _ _ h₁ h₂
    rw [e]; exact ⟨rfl, rfl⟩

end GlobalTheory.GamMul
