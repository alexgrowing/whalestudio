import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelForRootMetrics
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_model_for_root_metrics : ∀ (D : D7) (O : Setup D), O.Core → ∀ (B : ℝ), 2 ≤ B → ∀ c : O.s.Comp, ∃ (M : TrueGeo.Model (O.var c)) (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) (L : Option (DV.Rt D.what₂.Tau O.N) → HermLB M.p) (m : ℕ+), ∀ o : Option (DV.Rt D.what₂.Tau O.N), (o.elim (O.met.ab c) (O.root0 c (FlagAr.setB O.Y B))).Induced M (L o) m 0 := by
  first | exact @GlobalTheory.GenModel.exists_normal_model | exact GlobalTheory.GenModel.exists_normal_model | (intros; apply GlobalTheory.GenModel.exists_normal_model <;> assumption)
