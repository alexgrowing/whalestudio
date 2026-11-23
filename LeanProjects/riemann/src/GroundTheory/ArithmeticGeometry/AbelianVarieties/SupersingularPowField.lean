import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.Supersingular

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField

universe u

variable {F : Type u} [Field F] [DecidableEq F] (E E' : WeierstrassCurve F) (p : ℕ)
  [hp : Fact p.Prime] [CharP F p]

noncomputable def powFieldPoints :
    AddSubgroup (E'.baseChange E.toAffine.FunctionField).toAffine.Point :=
  (Point.map (W' := E') (powField E p).val).range

variable {E E'} [E.IsElliptic] [E'.IsElliptic]

omit [DecidableEq F] [E.IsElliptic] [E'.IsElliptic] in

theorem Isogeny.val_eq_some_x_y (φ : Isogeny E E') : φ.1 = Point.some φ.x φ.y φ.nonsingular := by
  obtain ⟨Q, ⟨x, y, h, rfl, -⟩, -⟩ := φ
  rfl

variable [IsAlgClosed F]

end GroundTheory.Arith.Abelian
