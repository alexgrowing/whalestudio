import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberGraphFiltrationLieOfMapIntoHodge
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoords
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualNumberGraphFiltration_lie_of_map_into_hodge : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (β : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s) (f : HdR o₀.A →ₗ[k] HdR o₀.A), GlobalTheory.HTCount.lieZ o₀ β ≤ Fil o₀.A → (∀ x ∈ GlobalTheory.HTCount.lieZ o₀ β, f x ∈ Fil o₀.A) → ∀ d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (epsDP k) (GlobalTheory.DeRham.epsRed k) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) d) - algebraMap k (DualNumber k) (β b.ρ) • d ∈ GlobalTheory.HTRealise.graphFil o₀.A f → ∃ w : Fin D.a → Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (epsDP k) (GlobalTheory.DeRham.epsRed k) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - algebraMap k (DualNumber k) (β (b.t i c)) • w i ∈ GlobalTheory.HTRealise.graphFil o₀.A f) ∧ d - ∑ i, w i ∈ GlobalTheory.HTRealise.graphFil o₀.A f := by
  first | (exact @GlobalTheory.HTRealise.eigen_decomp_graphFil) | (exact GlobalTheory.HTRealise.eigen_decomp_graphFil) | (intros; apply GlobalTheory.HTRealise.eigen_decomp_graphFil <;> assumption)
