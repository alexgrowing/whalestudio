import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.SepDefs

noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

def oLat (K : Type) [Field K] [NumberField K] (k : ℕ) : Submodule (𝓞 K) (Fin k → K) :=
  LinearMap.range (LinearMap.compLeft (Algebra.linearMap (𝓞 K) K) (Fin k))

def dualL {K : Type} [Field K] [NumberField K] {k : ℕ} (X : Submodule (𝓞 K) (Fin k → K)) :
    Submodule (𝓞 K) (Fin k → K) where
  carrier := {t | ∀ s ∈ X, s ⬝ᵥ t ∈ (algebraMap (𝓞 K) K).range}
  add_mem' := by
    intro a b ha hb s hs
    rw [Set.mem_setOf_eq] at ha hb
    rw [dotProduct_add]
    exact add_mem (ha s hs) (hb s hs)
  zero_mem' := by
    intro s _
    rw [dotProduct_zero]
    exact zero_mem _
  smul_mem' := by
    intro c t ht s hs
    rw [Set.mem_setOf_eq] at ht
    have h1 := ht (c • s) (X.smul_mem c hs)
    have h2 : s ⬝ᵥ (c • t) = (c • s) ⬝ᵥ t := by
      simp only [dotProduct, Pi.smul_apply, Algebra.smul_def]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [h2]
    exact h1

def DualIdx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (k : ℕ) (X Y : Submodule (𝓞 K) (Fin k → K)), X ≤ Y →
    X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0 →
    (dualL Y).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≠ 0 ∧
      (dualL Y).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≤ X.toAddSubgroup.relIndex Y.toAddSubgroup

def DetIdx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (k : ℕ) (N : Matrix (Fin k) (Fin k) K) (Q D : AddSubgroup (Fin k → K)),
    (oLat K k).toAddSubgroup ≤ Q → (oLat K k).toAddSubgroup.relIndex Q ≠ 0 →
    D ≤ (oLat K k).toAddSubgroup → D.relIndex (oLat K k).toAddSubgroup ≠ 0 →
    (∀ r ∈ D, ∃ s ∈ Q, s ᵥ* N = r) →
    |((Algebra.norm ℚ N.det : ℚ) : ℝ)| ≤
      ((oLat K k).toAddSubgroup.relIndex Q : ℝ) * (D.relIndex (oLat K k).toAddSubgroup : ℝ)

def IndexOf : Prop := DualIdx → DetIdx → IndexIneq

end PI.UnitaryGroupMassFormula.LCG
