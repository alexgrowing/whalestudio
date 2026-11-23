import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatSecDetDualTensorSupport
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ratSec_det_dual_tensor_support : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (F Q : X.Modules) (g' : VMetric p F 1) (g : VMetric p Q 1) (H' : g'.IsCInf) (H : g.IsCInf) (s : F ⟶ Q), s ≠ 0 → ∃ (r : ((VMetric.det H').dual.tens (VMetric.det H)).B.ι → X.functionFieldˣ) (hr : IsRatSec ((VMetric.det H').dual.tens (VMetric.det H)).B r), (∀ z ∈ (((VMetric.det H').dual.tens (VMetric.det H)).div hr).supp, VanishesAt s z) ∧ ∀ σ : k →+* ℂ, ∀ y ∈ offSupp p σ (((VMetric.det H').dual.tens (VMetric.det H)).div hr), ∀ (U : X.Opens) (t : Γ(F, U)), IsFrame (fun _ : Fin 1 => t) → y ∈ ptsIn p σ U → 0 < ((g.met σ).form (s.app U t) (s.app U t) y).re ∧ logNorm (((VMetric.det H').dual.tens (VMetric.det H)).φ σ) r y = Real.log (((g.met σ).form (s.app U t) (s.app U t) y).re / ((g'.met σ).form t t y).re) / 2 := by
  first | exact @GlobalTheory.LineHomSec.exists_ratSec | exact GlobalTheory.LineHomSec.exists_ratSec | (intros; apply GlobalTheory.LineHomSec.exists_ratSec <;> assumption)
