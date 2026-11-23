import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLocalUnitsAlongNilpotentThickening
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_local_units_along_nilpotent_thickening : ∀ (R : Type) [CommRing R] (J : Ideal R) (X X₀ : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (γ : X₀ ⟶ X) (q : X₀ ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback γ q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → Surjective γ → ∀ (L : LB X), L.IsLB → ∀ D : X.Opens, IsAffineOpen D → ∀ u : ∀ m : L.ι, Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, (∀ z m m', γ z ∈ D ⊓ L.U m → γ z ∈ D ⊓ L.U m' → gm (𝟙 X₀) z _ (u m) = gm γ z _ (L.g m m') * gm (𝟙 X₀) z _ (u m')) → ∃ τ : ∀ m : L.ι, Γ(X, D ⊓ L.U m)ˣ, (∀ m, (γ.app (D ⊓ L.U m)).hom (τ m).val = (u m).val) ∧ ∀ x m m', x ∈ D ⊓ L.U m → x ∈ D ⊓ L.U m' → gm (𝟙 X) x _ (τ m) = gm (𝟙 X) x _ (L.g m m') * gm (𝟙 X) x _ (τ m') := by
  first | exact @GlobalTheory.FormalAlg.lift_localUnits_of_thickening | exact GlobalTheory.FormalAlg.lift_localUnits_of_thickening | (intros; apply GlobalTheory.FormalAlg.lift_localUnits_of_thickening <;> assumption)
