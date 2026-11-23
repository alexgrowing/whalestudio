import Mathlib

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

namespace FibreMeasure

open MeasureTheory Topology Filter Set

section Chart

variable {G T : Type*}
  [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T] [LocallyCompactSpace T]
  [T2Space T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]

structure IsTransChart (dX : Measure G) (Γ : G → T) (Ω : Set G) (σ : T → G → G) : Prop where
  isOpen : IsOpen Ω
  continuousOn : ContinuousOn (fun q : T × G ↦ σ q.1 q.2) (univ ×ˢ Ω)
  mapsTo : ∀ s X, X ∈ Ω → σ s X ∈ Ω
  zero : ∀ X ∈ Ω, σ 0 X = X
  add : ∀ s t X, X ∈ Ω → σ s (σ t X) = σ (s + t) X
  shift : ∀ s X, X ∈ Ω → Γ (σ s X) = Γ X + s
  pres : ∀ s, MeasurePreserving (σ s) (dX.restrict Ω) (dX.restrict Ω)

variable {dX : Measure G} {Γ : G → T} {Ω : Set G} {σ : T → G → G}

variable (Γ σ) in

def chartProj (X : G) : G := σ (-Γ X) X

variable (Γ Ω σ) in

noncomputable def chartProjM : G → G := by
  classical exact Ω.piecewise (chartProj Γ σ) id

namespace IsTransChart

variable (h : IsTransChart dX Γ Ω σ)
include h

theorem Γ_chartProj {X : G} (hX : X ∈ Ω) : Γ (chartProj Γ σ X) = 0 := by
  rw [chartProj, h.shift _ _ hX, add_neg_cancel]

theorem σ_Γ_chartProj {X : G} (hX : X ∈ Ω) : σ (Γ X) (chartProj Γ σ X) = X := by
  rw [chartProj, h.add _ _ _ hX, add_neg_cancel, h.zero _ hX]

theorem chartProj_σ (s : T) {X : G} (hX : X ∈ Ω) :
    chartProj Γ σ (σ s X) = chartProj Γ σ X := by
  rw [chartProj, chartProj, h.shift _ _ hX, h.add _ _ _ hX]
  congr 1
  abel

theorem chartProj_of_Γ_eq_zero {X : G} (hX : X ∈ Ω) (h0 : Γ X = 0) : chartProj Γ σ X = X := by
  rw [chartProj, h0, neg_zero, h.zero _ hX]

end IsTransChart

end Chart

end FibreMeasure

end GroundTheory.Heights₂.Theta
