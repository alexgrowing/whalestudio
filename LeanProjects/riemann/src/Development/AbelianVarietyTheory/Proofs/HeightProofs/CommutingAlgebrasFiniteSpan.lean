import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MulApply
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.FiniteOrbit

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def orb (A : Subalgebra ℂ (Module.End ℂ M)) (x : M) : Submodule ℂ M :=
  Submodule.span ℂ {y : M | ∃ a ∈ A, y = a x}

theorem apply_mem_orb (A : Subalgebra ℂ (Module.End ℂ M)) (x : M) {a : Module.End ℂ M}
    (ha : a ∈ A) : a x ∈ orb A x :=
  Submodule.subset_span ⟨a, ha, rfl⟩

theorem orb_le {A : Subalgebra ℂ (Module.End ℂ M)} {x : M} {N : Submodule ℂ M}
    (h : ∀ a ∈ A, a x ∈ N) : orb A x ≤ N := by
  refine Submodule.span_le.2 ?_
  rintro y ⟨a, ha, rfl⟩
  exact h a ha

def finVec (A : Subalgebra ℂ (Module.End ℂ M)) : Submodule ℂ M where
  carrier := {x | FiniteDimensional ℂ (orb A x)}
  add_mem' := by
    intro x y hx hy
    have hx' : FiniteDimensional ℂ (orb A x) := hx
    have hy' : FiniteDimensional ℂ (orb A y) := hy
    have : orb A (x + y) ≤ orb A x ⊔ orb A y := orb_le fun a ha => by
      rw [map_add]
      exact Submodule.add_mem_sup (apply_mem_orb A x ha) (apply_mem_orb A y ha)
    exact Submodule.finiteDimensional_of_le this
  zero_mem' := by
    have : orb A (0 : M) ≤ ⊥ := orb_le fun a _ => by simp
    exact Submodule.finiteDimensional_of_le this
  smul_mem' := by
    intro c x hx
    have hx' : FiniteDimensional ℂ (orb A x) := hx
    have : orb A (c • x) ≤ orb A x := orb_le fun a ha => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (apply_mem_orb A x ha)
    exact Submodule.finiteDimensional_of_le this

def orbSub (A : Subalgebra ℂ (Module.End ℂ M)) (W : Submodule ℂ M) : Submodule ℂ M :=
  Submodule.span ℂ {y : M | ∃ a ∈ A, ∃ x ∈ W, y = a x}

theorem exists_finiteDimensional_stable (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type)
    [Finite ι] (A : ι → Subalgebra ℂ (Module.End ℂ M))
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a) (m : M)
    (hm : ∀ i, FiniteDimensional ℂ (Submodule.span ℂ {x : M | ∃ a ∈ A i, x = a m})) :
    ∃ W : Submodule ℂ M, FiniteDimensional ℂ W ∧ m ∈ W ∧ ∀ i, ∀ a ∈ A i, ∀ x ∈ W, a x ∈ W := by
  first
  | exact @_root_.GlobalTheory.OrbitGrowth.main
  | exact _root_.GlobalTheory.OrbitGrowth.main
  | (apply _root_.GlobalTheory.OrbitGrowth.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrbitGrowth.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrbitGrowth.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrbitGrowth.main ..)

end GlobalTheory.FiniteOrbit
