import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermFormConjDiag
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FrameHol

theorem isHolTo_precomp {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] {X : Scheme.{0}} {B : Set V} {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) {C : Set W}
    (hC : IsOpen C) {β : W → V} (hβ : DifferentiableOn ℂ β C) (hm : Set.MapsTo β C B) :
    IsHolTo C (fun w => y (β w)) := by
  unfold IsHolTo at h ⊢
  intro U f
  obtain ⟨hO, hD⟩ := h U f
  beta_reduce
  have hset : {w | w ∈ C ∧ ⊤ ≤ y (β w) ⁻¹ᵁ U} = C ∩ β ⁻¹' {b | b ∈ B ∧ ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext w
    constructor
    · rintro ⟨hw, hU⟩
      exact ⟨hw, hm hw, hU⟩
    · rintro ⟨hw, -, hU⟩
      exact ⟨hw, hU⟩
  rw [hset]
  exact ⟨hβ.continuousOn.isOpen_inter_preimage hC hO,
    hD.comp (hβ.mono Set.inter_subset_left) (fun w hw => hw.2)⟩

end GlobalTheory.FrameHol
