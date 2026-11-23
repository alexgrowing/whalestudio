import Mathlib

theorem UpperTheory.Reformulated.B.Qf45.isInt_conj :
    ∀ {O : Type} [inst : CommRing O]
    {B : Type} [inst_1 : Ring B] [inst_2 : Algebra O B] (a b k : B),
    a * b = (1 : B) → b * a = (1 : B) → IsIntegral O k → IsIntegral O (a * k * b) := by
  intro O _ B _ _ a b k hab hba hk
  let f : B →ₐ[O] B :=
    { toFun := fun x => a * x * b
      map_one' := by rw [mul_one, hab]
      map_mul' := fun x y => by
        calc a * (x * y) * b = a * x * (b * a) * y * b := by
              rw [hba, mul_one, mul_assoc a x y]
          _ = a * x * b * (a * y * b) := by simp only [mul_assoc]
      map_zero' := by rw [mul_zero, zero_mul]
      map_add' := fun x y => by rw [mul_add, add_mul]
      commutes' := fun r => by
        rw [← Algebra.commutes r a, mul_assoc, hab, mul_one] }
  exact hk.map f
