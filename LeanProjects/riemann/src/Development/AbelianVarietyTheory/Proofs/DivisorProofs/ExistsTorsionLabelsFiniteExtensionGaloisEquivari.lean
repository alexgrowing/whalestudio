import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsFinExtEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicKb
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_labels_finExt_galEqN : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A) (n : ℕ), OneTrait D.toPre A lab → GalEqN n lab → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁), FinExt ρ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)), Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left), IsFib ρ A A₁ a → 1 ≤ n → ∃ lab₁ : Labels D₁.toPre A₁, OneTrait D₁.toPre A₁ lab₁ ∧ GalEqN n lab₁ := by
  intro R _ _ _ hB D A lab n hOne hGal R₁ _ _ _ ρ hρ D₁ hD A₁ a hfib hn
  obtain ⟨hD⟩ := hD
  obtain ⟨_, em, lab₁, hc, hOne₁, hrel⟩ :=
    exists_labels_finExt_emb R hB D A lab hOne R₁ ρ hρ D₁ hD A₁ a hfib
  exact ⟨lab₁, hOne₁, LabBC.galEqN_of_rel ρ hρ D D₁ hD A A₁ a hfib lab n hn hGal em lab₁ hc hrel⟩

end GlobalTheory.Mum
