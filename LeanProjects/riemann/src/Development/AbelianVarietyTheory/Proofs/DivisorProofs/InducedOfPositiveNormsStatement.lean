import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedOfPositiveNorms
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_of_positive_norms : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) (L : HermLB M.p) (k : ℕ+), (∀ σ z, PosAt (A.m σ) z) → Norms (Cover.ofModel M hM) L (fun x => genAt A.D x ^ (k : ℕ)) (fun σ y => (k : ℕ) * lnAdl A σ y) (fun v e y => (k : ℕ) * A.lg v e y) → A.Induced M L k 0 := by
  first | exact @GlobalTheory.CoverNorm.induced_of_norms | exact GlobalTheory.CoverNorm.induced_of_norms | (intros; apply GlobalTheory.CoverNorm.induced_of_norms <;> assumption)
