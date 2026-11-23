import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorGeneratesChartEstimate
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_generates_chart_estimate : Hypotheses2 → HypothesesH → OnObj fun D O _ T _ h => ∀ (c : O.Y.Comp) (a : Fin ((T.M c).n + 1)) (ψ : OpenPartialHomeomorph ((T.M c).X a) (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ)), IsCompatChart ((T.M c).A a) ψ → ∀ z ∈ ψ.target, ∀ R : ℝ, 2 ≤ R → ∀ (u : D.what₂.Tau → Fin O.Y.N → ℝ) (f : DV.Rt D.what₂.Tau O.N → (O.var c).Fn), (∀ y, (GlobalTheory.ShFam.Pad.divOf (O.Φ.C c) (O.ex y)).GeneratesAt (under ((h.man c).pt a (ψ.symm z))) (f y)) → ∀ w, levi (((T.F c).th u a + LocPot.ofFun ((T.F c).phR R u a)).φ (ψ.symm z) ∘ ψ.symm) z w = levi (fun v => ∑ y : DV.Rt D.what₂.Tau O.N, u y.1 y.2 * lnN (O.met.hm c (some R) ((h.man c).ε a) (O.ex y)) (f y) ((h.man c).pt a (ψ.symm v))) z w := by
  first | exact @GlobalTheory.LeviRedInterp.levi_th_add_phR | exact GlobalTheory.LeviRedInterp.levi_th_add_phR | (intros; apply GlobalTheory.LeviRedInterp.levi_th_add_phR <;> assumption)
