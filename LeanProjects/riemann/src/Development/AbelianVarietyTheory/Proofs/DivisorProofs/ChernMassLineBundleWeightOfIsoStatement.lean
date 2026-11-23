import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassLineBundleWeightOfIso
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernMass_lineBundleWeightOfIso : ∀ (Y : Var ℂ) (L A : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L) (hA : A.IsLB) (w : L.Iso A) (hw : w.IsGen), φ.IsCInf → (φ.ofIso hA w hw).IsCInf ∧ Weight.chernInt (φ.ofIso hA w hw) Y.dim Set.univ (fun _ => 1) = Weight.chernInt φ Y.dim Set.univ (fun _ => 1) := by
  first | exact @GlobalTheory.ChernIso.chernMass_ofIso | exact GlobalTheory.ChernIso.chernMass_ofIso | (intros; apply GlobalTheory.ChernIso.chernMass_ofIso <;> assumption)
