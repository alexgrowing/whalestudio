import Mathlib
import GroundTheory.AutomorphicForms.GKModules.GKModule
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.MultOne
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.MultOneC
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.KTypeExist
import GroundTheory.AutomorphicForms.HarishChandraRegularity.CartanBasis

namespace GroundTheory.Automorphic

namespace UnitaryAdmissible

open MeasureTheory Module

section KHom

variable {K : Type*} [Monoid K] {W : Type*} [AddCommGroup W] [Module ℂ W]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {τ : Representation ℂ K W} {ρ : Representation ℂ K V}

theorem kHom_apply {T : W →ₗ[ℂ] V} (hT : T ∈ kHom τ ρ) (k : K) (w : W) :
    T (τ k w) = ρ k (T w) :=
  congrArg (fun f : W →ₗ[ℂ] V => f w) (hT k)

def kerSubrep {T : W →ₗ[ℂ] V} (hT : T ∈ kHom τ ρ) : Subrepresentation τ where
  toSubmodule := LinearMap.ker T
  apply_mem_toSubmodule k w hw := by
    simp only [LinearMap.mem_ker] at hw ⊢
    rw [kHom_apply hT, hw, map_zero]

theorem nontrivial_of_isIrreducible [τ.IsIrreducible] : Nontrivial W := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have hne : (⊥ : Subrepresentation τ) ≠ ⊤ := bot_ne_top
  apply hne
  apply Subrepresentation.toSubmodule_injective
  ext w
  simp [Subsingleton.elim w 0]

end KHom

section Integral

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [CompleteSpace E']

end Integral

section GL2R

open ArchWhittaker

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end GL2R

section GL2C

open ArchWhittakerC ArchWhittakerC.KT Complex
open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end GL2C

end UnitaryAdmissible

end GroundTheory.Automorphic
