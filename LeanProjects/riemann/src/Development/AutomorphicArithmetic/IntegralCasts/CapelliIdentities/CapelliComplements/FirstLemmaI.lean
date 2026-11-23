import Mathlib

universe u_1

namespace Bl.MatrixMapSub

theorem goal1 :
  ∀ {A : Type u_1} [inst : CommRing.{u_1} A] {d : Nat} (σ : RingHom.{u_1, u_1} A A)
  (X Y : Matrix.{0, 0, u_1} (Fin d) (Fin d) A),
  Eq.{u_1 + 1}
    (Matrix.map.{u_1, u_1, 0, 0} (HSub.hSub.{u_1, u_1, u_1} X Y) (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ))
    (HSub.hSub.{u_1, u_1, u_1} (Matrix.map.{u_1, u_1, 0, 0} X (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ))
      (Matrix.map.{u_1, u_1, 0, 0} Y (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ))) := by
  intro A _ d σ X Y
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]

end Bl.MatrixMapSub
