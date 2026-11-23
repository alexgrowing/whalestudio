import Mathlib
import GroundTheory.AutomorphicForms.UnitaryRepresentations.IsInvariantIffCommuteStarProjection
import GroundTheory.AutomorphicForms.UnitaryRepresentations.ExistsEqAlgebraMapOfIsSelfAdjoint
import GroundTheory.AutomorphicForms.UnitaryRepresentations.DirectSum
import GroundTheory.AutomorphicForms.UnitaryRepresentations.Integrated

namespace GroundTheory.Automorphic

namespace UnitaryRep

open scoped InnerProductSpace
open ContinuousLinearMap Submodule

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

variable {π : UnitaryRep G H}

lemma IsInvariant.iSup {ι : Sort*} {V : ι → Submodule ℂ H} (h : ∀ i, π.IsInvariant (V i)) :
    π.IsInvariant (⨆ i, V i) := by
  intro g v hv
  exact Submodule.iSup_induction V (motive := fun x => π g x ∈ ⨆ i, V i) hv
    (fun i x hx => Submodule.mem_iSup_of_mem i (h i g x hx)) (by simp)
    (fun x y hx hy => by simpa using add_mem hx hy)

variable (π) in

def isotypic (σ : UnitaryRep G K) : Submodule ℂ H :=
  (⨆ T ∈ σ.intertwiners π, LinearMap.range (T : K →ₗ[ℂ] H)).topologicalClosure

lemma isClosed_isotypic (σ : UnitaryRep G K) : IsClosed (π.isotypic σ : Set H) := by
  unfold isotypic
  exact Submodule.isClosed_topologicalClosure _

instance (σ : UnitaryRep G K) : CompleteSpace (π.isotypic σ) :=
  (isClosed_isotypic σ).completeSpace_coe

section decomposition

variable {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]

lemma top_le_topologicalClosure_iSup
    (hV : IsHilbertSum ℂ (fun j => V j) fun j => (V j).subtypeₗᵢ) :
    ⊤ ≤ (⨆ j, V j).topologicalClosure := by
  have h1 : LinearMap.range hV.OrthogonalFamily.linearIsometry.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hV.surjective_isometry
  rw [hV.OrthogonalFamily.range_linearIsometry] at h1
  simpa [Submodule.subtypeₗᵢ_toLinearMap, Submodule.range_subtype] using h1.ge

end decomposition

end UnitaryRep

end GroundTheory.Automorphic
