import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParameterTransferTypes

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links NumberField

namespace GlobalTheory.LiftOntoCompare

section Hilbert

variable {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (θ : V →ₗ[ℂ] W) {X : Submodule ℂ V} {M : Submodule ℂ W}

theorem disjoint_map_adjoint_ker (M : Submodule ℂ W) : Disjoint (M.map (LinearMap.adjoint θ)) (LinearMap.ker θ) := by
  rw [Submodule.disjoint_def]
  rintro _ ⟨m, -, rfl⟩ h
  have h0 : θ (LinearMap.adjoint θ m) = 0 := h
  have : inner ℂ (LinearMap.adjoint θ m) (LinearMap.adjoint θ m) = 0 := by
    rw [LinearMap.adjoint_inner_left, h0, inner_zero_right]
  exact inner_self_eq_zero.1 this

end Hilbert

section Readings

open GlobalTheory.IndefiniteRowSideFullHecke.ParameterTransferTypes

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
  (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ)

def PartsMatchAt : Prop :=
  ∀ c ∈ IxW R i t P, ∀ c', Transfer R i t P c c' →
    (projectedFormsSystemPart R i t P c').map (R.thG i t) ≤ MWc R i t P c ∧ (MWc R i t P c).map (thStar R i t) ≤ projectedFormsSystemPart R i t P c'

def GoodMatchAt : Prop :=
  (V0 R i t P).map (R.thG i t) ≤ MW R i P ∧ (MW R i P).map (thStar R i t) ≤ V0 R i t P

end Readings

example : ∃ θ : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] ℂ, (⊤ : Submodule ℂ _).map θ = ⊤ ∧
    (⊤ : Submodule ℂ ℂ).map (LinearMap.adjoint θ) ≠ ⊤ := by
  refine ⟨(EuclideanSpace.projₗ (0 : Fin 2)), ?_, fun h => ?_⟩
  · rw [eq_top_iff]
    intro z _
    exact ⟨EuclideanSpace.single 0 z, trivial, by simp⟩
  · have := disjoint_map_adjoint_ker (EuclideanSpace.projₗ (0 : Fin 2) : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] ℂ) ⊤
    rw [h, Submodule.disjoint_def] at this
    have h1 := this (EuclideanSpace.single 1 1) trivial (by simp)
    have h2 := congrArg (fun v : EuclideanSpace ℂ (Fin 2) => v 1) h1
    simp at h2

end GlobalTheory.LiftOntoCompare

end
