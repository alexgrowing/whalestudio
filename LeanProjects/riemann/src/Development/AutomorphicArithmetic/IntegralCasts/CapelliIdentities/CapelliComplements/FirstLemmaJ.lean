import Mathlib

universe u_1

namespace Bl.MatrixMapSmul

theorem goal1 :
  ∀ {A : Type u_1} [inst : CommRing.{u_1} A] {d : Nat} (σ : RingHom.{u_1, u_1} A A) (a : A)
  (X : Matrix.{0, 0, u_1} (Fin d) (Fin d) A),
  Eq.{u_1 + 1}
    (Matrix.map.{u_1, u_1, 0, 0} (HSMul.hSMul.{u_1, u_1, u_1} a X) (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ))
    (HSMul.hSMul.{u_1, u_1, u_1} (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ a)
      (Matrix.map.{u_1, u_1, 0, 0} X (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ))) := by
  intro A _ d σ a X
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

end Bl.MatrixMapSmul
