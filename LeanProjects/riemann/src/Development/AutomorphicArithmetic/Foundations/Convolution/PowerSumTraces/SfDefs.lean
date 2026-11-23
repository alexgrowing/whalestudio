import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import GroundTheory.AutomorphicForms.SmoothRep

noncomputable section

open GroundTheory.Automorphic
open scoped InnerProductSpace

namespace UpperTheory.ConvolutionTheory.C.Sf

variable {G : Type} [Group G] [TopologicalSpace G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {S : Type} [AddCommGroup S] [Module ℂ S]

def fixU (π : UnitaryRep G H) (U : Subgroup G) : Submodule ℂ H where
  carrier := {v | ∀ u ∈ U, π u v = v}
  add_mem' {a b} ha hb u hu := by rw [map_add, ha u hu, hb u hu]
  zero_mem' u _ := map_zero _
  smul_mem' c v hv u hu := by rw [map_smul, hv u hu]

theorem mem_fixU {π : UnitaryRep G H} {U : Subgroup G} {v : H} : v ∈ fixU π U ↔ ∀ u ∈ U, π u v = v := Iff.rfl

theorem isClosed_fixU (π : UnitaryRep G H) (U : Subgroup G) : IsClosed (fixU π U : Set H) := by
  have : (fixU π U : Set H) = ⋂ u ∈ U, {v | π u v = v} := by
    ext v
    simp [mem_fixU]
  rw [this]
  exact isClosed_biInter fun u _ => isClosed_eq (π u).continuous continuous_id

structure Eqv (τ : Representation ℂ G S) (π : UnitaryRep G H) (D : Submodule ℂ H) (f : S →ₗ[ℂ] H) : Prop where
  mem : ∀ x, f x ∈ D
  map : ∀ g x, f (τ g x) = π g (f x)

def spanAll (τ : Representation ℂ G S) (π : UnitaryRep G H) (D : Submodule ℂ H) : Submodule ℂ H :=
  Submodule.span ℂ {y | ∃ f, Eqv τ π D f ∧ ∃ x, y = f x}

def spanFix (τ : Representation ℂ G S) (π : UnitaryRep G H) (D : Submodule ℂ H) (U : Subgroup G) : Submodule ℂ H :=
  Submodule.span ℂ {y | ∃ f, Eqv τ π D f ∧ ∃ x ∈ fixedVectors τ U, y = f x}

def IsOp [MeasurableSpace G] (π : UnitaryRep G H) (m : MeasureTheory.Measure G) (φ : G → ℂ) (T : H →L[ℂ] H) : Prop :=
  ∀ u v : H, ⟪u, T v⟫_ℂ = ∫ g, φ g * ⟪u, π g v⟫_ℂ ∂m

end UpperTheory.ConvolutionTheory.C.Sf
