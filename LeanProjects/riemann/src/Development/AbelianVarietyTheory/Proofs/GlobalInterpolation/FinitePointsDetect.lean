import Mathlib

namespace GlobalTheory.FinitePointsDetect

theorem finite_points_detect : ∀ {X : Type} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥W],
    ∃ (s : Finset X), ∀ (v : ↥W), (∀ x ∈ s, (↑v : X → ℂ) x = (0 : ℂ)) → v = (0 : ↥W) := by
  intro X W _
  classical
  let ev : X → (W →ₗ[ℂ] ℂ) := fun x => (LinearMap.proj x).comp W.subtype
  let K : Finset X → Submodule ℂ W := fun s => ⨅ x ∈ s, LinearMap.ker (ev x)
  obtain ⟨_, ⟨s, rfl⟩, hs⟩ :=
    (wellFounded_lt (α := Submodule ℂ W)).has_min (Set.range K) ⟨K ∅, ∅, rfl⟩
  have key : ∀ v ∈ K s, ∀ y : X, (↑v : X → ℂ) y = 0 := by
    intro v hv y
    have hle : K (insert y s) ≤ K s := by
      intro w hw
      simp only [K, Submodule.mem_iInf] at hw ⊢
      intro x hx
      exact hw x (Finset.mem_insert_of_mem hx)
    have heq : K (insert y s) = K s := eq_of_le_of_not_lt hle (hs _ ⟨_, rfl⟩)
    rw [← heq] at hv
    simp only [K, Submodule.mem_iInf] at hv
    have := hv y (Finset.mem_insert_self y s)
    simpa [ev] using this
  refine ⟨s, fun v hv => ?_⟩
  have hvK : v ∈ K s := by
    simp only [K, Submodule.mem_iInf]
    intro x hx
    simpa [ev] using hv x hx
  apply Subtype.ext
  funext y
  simpa using key v hvK y

end GlobalTheory.FinitePointsDetect
