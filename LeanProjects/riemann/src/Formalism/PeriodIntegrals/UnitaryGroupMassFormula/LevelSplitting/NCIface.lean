import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCDefs

noncomputable section

namespace PI.LevelKSplit.W.NC

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def HeisP : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
  ∃ sH : (Fin r → Wp (Af F) σ J P) → HA (Af F) σ J,
    Continuous sH ∧ Continuous (yH (Af F) σ J P) ∧
    (∀ y, sH y ∈ LevelUnipotentSubgroup (Af F) σ J P) ∧
    (∀ n ∈ LevelUnipotentSubgroup (Af F) σ J P, ∃ y : Fin r → Wp (Af F) σ J P,
      (∀ a, (y a : Fin M → Af F ⊗[F] E) = yH (Af F) σ J P n a) ∧ (sH y)⁻¹ * n ∈ Zsub (Af F) σ J P) ∧
    (∀ y, ∀ z ∈ Zsub (Af F) σ J P, ∀ a, yH (Af F) σ J P (sH y * z) a = y a) ∧
    Zsub (Af F) σ J P ≤ LevelUnipotentSubgroup (Af F) σ J P ∧
    (∀ z ∈ Zsub (Af F) σ J P, ∀ n ∈ LevelUnipotentSubgroup (Af F) σ J P, z * n = n * z) ∧
    (∀ y y', sH y * sH y' * (sH (y + y'))⁻¹ ∈ Zsub (Af F) σ J P) ∧
    (∀ n ∈ Nsub (Af F) σ J P, ∀ z ∈ Zsub (Af F) σ J P, n * z * n⁻¹ ∈ Zsub (Af F) σ J P) ∧
    (∀ h ∈ Hsub (Af F) σ J P, ∀ y, ∃ y' : Fin r → Wp (Af F) σ J P,
      (∀ a, (y' a : Fin M → Af F ⊗[F] E) = lin (Af F) σ J h (y a)) ∧ h * sH y * h⁻¹ = sH y') ∧
    (∀ h ∈ Hsub (Af F) σ J P, ∀ z ∈ Zsub (Af F) σ J P, h * z * h⁻¹ = z)

def LevP : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
  ∃ (A : Subgroup (HA (Af F) σ J)) (Lev : HA (Af F) σ J → HA (Af F) σ J),
    A ≤ Nsub (Af F) σ J P ∧ IsClosed (A : Set (HA (Af F) σ J)) ∧ Continuous Lev ∧
    (∀ n ∈ Nsub (Af F) σ J P, Lev n ∈ A ∧ (Lev n)⁻¹ * n ∈ LevelUnipotentSubgroup (Af F) σ J P) ∧
    (∀ u ∈ A, u ∈ LevelUnipotentSubgroup (Af F) σ J P → u = 1) ∧
    (∀ n ∈ Nsub (Af F) σ J P, ∀ m ∈ LevelUnipotentSubgroup (Af F) σ J P, n * m * n⁻¹ ∈ LevelUnipotentSubgroup (Af F) σ J P) ∧
    (∀ h ∈ Hsub (Af F) σ J P, ∀ u ∈ A, h * u = u * h)

end Ext

def HeisPAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => HeisP F E σ M J
def LevPAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => LevP F E σ M J

end PI.LevelKSplit.W.NC
