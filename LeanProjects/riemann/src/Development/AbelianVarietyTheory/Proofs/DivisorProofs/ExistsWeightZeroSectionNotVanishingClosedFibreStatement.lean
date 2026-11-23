import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroSectionNotVanishingClosedFibre
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weightZero_section_not_vanishing_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (k : ℕ), 2 ≤ k → ∀ x : D.toPre.P.A.left,
      D.toPre.P.A.hom x = closedPoint R →
      ∃ (σ : D.toPre.SecB k 0) (j : Fin 4 → D.toPre.P.L.ι), x ∈ D.toPre.P.A.left.basicOpen (σ.f j) := by
  first | exact @GlobalTheory.Mum.exists_secB_zero_mem_basicOpen | exact GlobalTheory.Mum.exists_secB_zero_mem_basicOpen | (intros; apply GlobalTheory.Mum.exists_secB_zero_mem_basicOpen <;> assumption)
