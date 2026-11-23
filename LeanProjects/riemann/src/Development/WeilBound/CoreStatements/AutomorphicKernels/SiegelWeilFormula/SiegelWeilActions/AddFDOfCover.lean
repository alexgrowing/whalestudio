import Mathlib
import GroundTheory.HeightsAndTheta.Theta.FundDomain

noncomputable section

open MeasureTheory Set Topology

namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

theorem addFD_of_cover {A : Type} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [T2Space A] [MeasurableSpace A] [BorelSpace A] (Γ : AddSubgroup A) [DiscreteTopology Γ] {C : Set A} (hC : IsCompact C)
    (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ C) :
    ∃ 𝓕 : Set A, MeasurableSet 𝓕 ∧ IsCompact (closure 𝓕) ∧ ∀ x, ∃! γ : Γ, γ +ᵥ x ∈ 𝓕 := by
  classical
  letI mA : MeasurableSpace (Multiplicative A) := ‹MeasurableSpace A›
  haveI : BorelSpace (Multiplicative A) := ⟨BorelSpace.measurable_eq (α := A)⟩
  haveI : LocallyCompactSpace (Multiplicative A) := inferInstanceAs (LocallyCompactSpace A)
  let Γm : Subgroup (Multiplicative A) := AddSubgroup.toSubgroup Γ
  have memΓm : ∀ x : Multiplicative A, x ∈ Γm ↔ Multiplicative.toAdd x ∈ Γ := fun x => Iff.rfl
  let g : Γm → Γ := fun x => ⟨Multiplicative.toAdd x.1, (memΓm x.1).1 x.2⟩
  have hg : Continuous g := (continuous_toAdd.comp continuous_subtype_val).subtype_mk _
  have hgi : Function.Injective g := fun x y h => Subtype.ext (by
    have := congrArg Subtype.val h
    exact Multiplicative.toAdd.injective this)
  haveI : DiscreteTopology Γm := DiscreteTopology.of_continuous_injective hg hgi
  have hC' : IsCompact (Multiplicative.ofAdd '' C) := hC.image continuous_ofAdd
  have hcov' : ∀ x : Multiplicative A, ∃ γ ∈ Γm, γ * x ∈ Multiplicative.ofAdd '' C := by
    intro x
    obtain ⟨γ, hγ, hγC⟩ := hcov (Multiplicative.toAdd x)
    exact ⟨Multiplicative.ofAdd γ, hγ, γ + Multiplicative.toAdd x, hγC, rfl⟩
  obtain ⟨𝓕, L, hm, hL, hsub, hu⟩ :=
    GroundTheory.Heights₂.Theta.exists_isFundamentalDomain_of_isCompact (G := Multiplicative A) Γm hC' hcov'
  let L' : Set A := Multiplicative.toAdd '' L
  have hL' : IsCompact L' := hL.image continuous_toAdd
  refine ⟨Multiplicative.ofAdd ⁻¹' 𝓕, hm, hL'.of_isClosed_subset isClosed_closure ?_, fun x => ?_⟩
  · refine closure_minimal (fun y hy => ⟨Multiplicative.ofAdd y, hsub hy, rfl⟩) hL'.isClosed
  · obtain ⟨γ, hγ, huniq⟩ := hu (Multiplicative.ofAdd x)
    refine ⟨g γ, hγ, fun γ' hγ' => ?_⟩
    have h1 : (⟨Multiplicative.ofAdd γ'.1, γ'.2⟩ : Γm) = γ := huniq _ hγ'
    apply Subtype.ext
    rw [← h1]
    rfl

theorem addFD_of_cover' {A : Type} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [T2Space A] [MeasurableSpace A] [BorelSpace A] (Γ : AddSubgroup A) [DiscreteTopology Γ] {C : Set A} (hC : IsCompact C)
    (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ C) (μ : Measure A) :
    ∃ 𝓕 : Set A, IsAddFundamentalDomain Γ 𝓕 μ ∧ IsCompact (closure 𝓕) := by
  obtain ⟨𝓕, hm, hc, hu⟩ := addFD_of_cover Γ hC hcov
  exact ⟨𝓕, IsAddFundamentalDomain.mk' hm.nullMeasurableSet hu, hc⟩

end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

end
