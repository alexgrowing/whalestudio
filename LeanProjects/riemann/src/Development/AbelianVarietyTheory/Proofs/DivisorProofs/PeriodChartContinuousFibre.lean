import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

namespace GlobalTheory.ThetaRR

theorem continuous_ex_fibre : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (P : PPAS S) (h : VMetric p (omega P.A) P.g) (σ : k →+* ℂ) (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ) (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ), IsPeriodChart h c τ ex → ∀ v ∈ c.e.target, Continuous fun z : Fin P.g → ℂ => ex (v, z) := by
  intro k _ S p P h σ c τ ex H v hv
  have hh := H.2.1
  have hj : Continuous fun z : Fin P.g → ℂ => ((v, z) : Pt (V 1) P.g) := by fun_prop
  rw [CxPts.continuous_iff]
  intro U
  refine ⟨?_, fun f => ?_⟩
  · convert (hh U 0).1.preimage hj using 1
    ext z
    exact ⟨fun hb => ⟨⟨hv, trivial⟩, hb⟩, fun hb => hb.2⟩
  · exact (hh U f).2.continuousOn.comp hj.continuousOn fun z hb => ⟨⟨hv, trivial⟩, hb⟩

end GlobalTheory.ThetaRR
