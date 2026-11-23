import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentsMemOfSumMemDistinctEigencharactersMod
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFilHtObject
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationOrderStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedPullConstMorVPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.components_mem_of_sum_mem_distinct_eigencharacters_mod : ∀ (k : Type) [Field k] (H : Type 1) [AddCommGroup H] [Module k H] (O : Type) [CommRing O] (ρ : O →+* Module.End k H) (F : Submodule k H), (∀ c, ∀ x ∈ F, ρ c x ∈ F) → ∀ (a : ℕ) (χ : Fin a → O → k), (∀ i j, i ≠ j → ∃ c, χ i c ≠ χ j c) → ∀ u : Fin a → H, (∀ i c, ρ c (u i) - χ i c • u i ∈ F) → ∑ i, u i ∈ F → ∀ i, u i ∈ F := by
  first | (exact @GlobalTheory.eigen_mod_stable) | (exact GlobalTheory.eigen_mod_stable) | (intros; apply GlobalTheory.eigen_mod_stable <;> assumption)
