import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateWeightDoubling
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tate_weight_doubling : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (f : X ⟶ X) (hf : f ≫ p = p) (L : HermLB p) (w : LB.Iso (L.pull f hf).B (L.pow 4).B), w.IsGen → ∃ u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ, (∀ σ, Continuous (u σ)) ∧ (∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) ∧ IsTate f hf L w u := by
  first | exact @GlobalTheory.ThetaRR.exists_isTate_continuous | exact GlobalTheory.ThetaRR.exists_isTate_continuous | (intros; apply GlobalTheory.ThetaRR.exists_isTate_continuous <;> assumption)
