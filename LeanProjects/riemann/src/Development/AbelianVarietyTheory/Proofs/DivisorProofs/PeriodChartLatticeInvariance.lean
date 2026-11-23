import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

namespace GlobalTheory.PeriodChartLattice

theorem ex_transl_eq : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (P : PPAS S) (h : VMetric p (omega P.A) P.g) (σ : k →+* ℂ) (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ) (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ), IsPeriodChart h c τ ex → ∀ l ∈ stdLat P.g, ∀ Q ∈ cov c.e.target P.g, ex (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.transl τ l Q) = ex Q := by
  intro k _ S p P h σ c τ ex H l hl Q hQ
  obtain ⟨v, z⟩ := Q
  have hv : v ∈ c.e.target := hQ.1
  have H' := (IsPeriodChart.isUnifChart H).2.2 v hv
  exact (H'.2.2 (z + GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.per (τ v) l) z).2 ⟨l, hl, rfl⟩

end GlobalTheory.PeriodChartLattice
