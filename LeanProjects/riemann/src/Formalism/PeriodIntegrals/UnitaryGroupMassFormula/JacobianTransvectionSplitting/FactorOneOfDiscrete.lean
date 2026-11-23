import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeNGLQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianTransvectionSplitting.DiscreteHaar

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace PI.NglqJacSplitW

section Mod

variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  [LocallyCompactSpace F]

theorem modF_of_ne {a : F} (h : a ≠ 0) :
    modF F a = ((distribHaarChar F (Units.mk0 a h) : ℝ≥0) : ℝ≥0∞) := by
  rw [modF, dif_neg h]

theorem modF_mul {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : modF F (a * b) = modF F a * modF F b := by
  rw [modF_of_ne (mul_ne_zero ha hb), modF_of_ne ha, modF_of_ne hb,
    show Units.mk0 (a * b) (mul_ne_zero ha hb) = Units.mk0 a ha * Units.mk0 b hb from Units.ext rfl, map_mul]
  push_cast
  rfl

end Mod

def rmul {E : Type} [CommRing E] (n m : ℕ) (A : Matrix (Fin m) (Fin m) E) :
    Matrix (Fin n) (Fin m) E →ₗ[E] Matrix (Fin n) (Fin m) E where
  toFun X := X * A
  map_add' X Y := Matrix.add_mul X Y A
  map_smul' c X := Matrix.smul_mul c X A

def lmulM {E : Type} [CommRing E] (m : ℕ) (B : Matrix (Fin m) (Fin m) E) :
    Matrix (Fin m) (Fin m) E →ₗ[E] Matrix (Fin m) (Fin m) E where
  toFun H := B * H
  map_add' X Y := Matrix.mul_add B X Y
  map_smul' c X := Matrix.mul_smul B c X

def pairEquiv (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] (n m : ℕ) :
    (Matrix (Fin n) (Fin m) F × Matrix (Fin n) (Fin m) F) ≃L[F]
      ((Fin n × Fin m) ⊕ (Fin n × Fin m) → F) where
  toFun X i := Sum.elim (fun p => X.1 p.1 p.2) (fun p => X.2 p.1 p.2) i
  invFun v := (Matrix.of fun a b => v (Sum.inl (a, b)), Matrix.of fun a b => v (Sum.inr (a, b)))
  map_add' X Y := by ext i; rcases i with p | p <;> rfl
  map_smul' c X := by ext i; rcases i with p | p <;> rfl
  left_inv X := by ext <;> rfl
  right_inv v := by ext i; rcases i with p | p <;> rfl
  continuous_toFun := by
    refine continuous_pi fun i => ?_
    rcases i with p | p
    · exact (continuous_fst.matrix_elem p.1 p.2)
    · exact (continuous_snd.matrix_elem p.1 p.2)
  continuous_invFun := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_pi fun a => continuous_pi fun b => continuous_apply (Sum.inl (a, b))
    · exact continuous_pi fun a => continuous_pi fun b => continuous_apply (Sum.inr (a, b))

def sqEquiv (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] (m : ℕ) :
    Matrix (Fin m) (Fin m) F ≃L[F] (Fin m × Fin m → F) where
  toFun X p := X p.1 p.2
  invFun v := Matrix.of fun a b => v (a, b)
  map_add' X Y := rfl
  map_smul' c X := rfl
  left_inv X := rfl
  right_inv v := rfl
  continuous_toFun := continuous_pi fun p => continuous_id.matrix_elem p.1 p.2
  continuous_invFun := continuous_pi fun a => continuous_pi fun b => continuous_apply (a, b)

end PI.NglqJacSplitW
