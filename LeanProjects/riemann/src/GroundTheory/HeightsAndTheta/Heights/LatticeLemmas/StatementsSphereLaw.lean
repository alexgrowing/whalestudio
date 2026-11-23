import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.IsProbabilityMeasureSphereLaw
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ProbabilityTheory

noncomputable section

def SphereLawBasic.Statement : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    IsProbabilityMeasure (sphereLaw N) ∧
    (∀ᵐ z ∂sphereLaw N, ∑ j, ‖z j‖ ^ 2 = 1) ∧
    ∀ S : Submodule ℂ (Fin N → ℂ), S ≠ ⊤ → sphereLaw N (S : Set (Fin N → ℂ)) = 0

def SphereLawUnitary.Statement : Prop :=
  ∀ (N : ℕ) (U : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)),
    (∀ v, ∑ j, ‖U v j‖ ^ 2 = ∑ j, ‖v j‖ ^ 2) → (sphereLaw N).map U = sphereLaw N

def SphereLawFirstCoord.Statement : Prop :=
  ∀ (N : ℕ) (hN : 2 ≤ N),
    (sphereLaw N).map (fun z ↦ ‖z ⟨0, by omega⟩‖ ^ 2) =
      volume.withDensity fun x ↦
        ENNReal.ofReal (Set.indicator (Set.Icc 0 1) (fun x ↦ (N - 1 : ℝ) * (1 - x) ^ (N - 2)) x)

def SpherePhase.Statement : Prop :=
  ∀ (N : ℕ) (p : Fin N → ℂ), ∑ j, ‖p j‖ ^ 2 = 1 → 2 ≤ N →
    (sphereLaw N).map (fun z ↦ (Complex.arg (coordAlong p z), (‖coordAlong p z‖, orthoDir p z))) =
      phaseLaw.prod ((sphereLaw N).map fun z ↦ (‖coordAlong p z‖, orthoDir p z))

example : ∃ U : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ),
    U ≠ LinearMap.id ∧ ∀ v, ∑ j, ‖U v j‖ ^ 2 = ∑ j, ‖v j‖ ^ 2 := by
  refine ⟨Complex.I • LinearMap.id, fun h ↦ ?_, fun v ↦ ?_⟩
  · have := congrArg (fun U : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) ↦ U (Pi.single 0 1) 0) h
    simp [Complex.ext_iff] at this
  · simp

example : ∑ j, ‖(Pi.single 0 1 : Fin 2 → ℂ) j‖ ^ 2 = 1 := by
  simp [Fin.sum_univ_two]

example : Submodule.span ℂ {(Pi.single 0 1 : Fin 2 → ℂ)} ≠ ⊤ := by
  intro h
  have hmem : (Pi.single 1 1 : Fin 2 → ℂ) ∈ Submodule.span ℂ {(Pi.single 0 1 : Fin 2 → ℂ)} :=
    h ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have := congrFun hc 1
  simp at this

end

end GroundTheory.Heights₂.Heights
