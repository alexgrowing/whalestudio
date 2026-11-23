import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenspaceDimensionOfUniformization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEigSp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenspace_dimension_of_uniformization : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL (D' : PLat D.O D.inv) t Q e, UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → ∀ τ : Fin D.a → (D.F →+* ℂ), (∀ i (c : 𝓞 D.F), τ i (c : D.F) = σ (b.t i c)) → (∀ i, Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i)) = D.m) ∧ ∀ u : Fin D.g → ℂ, ρ (algebraMap (𝓞 D.F) D.O D.ω) *ᵥ u = σ b.ρ • u → u ∈ ⨆ i, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i) := by
  first | exact @GlobalTheory.UPel.HT.LieType.lieEigen_rank_cover | exact GlobalTheory.UPel.HT.LieType.lieEigen_rank_cover | (intros; apply GlobalTheory.UPel.HT.LieType.lieEigen_rank_cover <;> assumption)
