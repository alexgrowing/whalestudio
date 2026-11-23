import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNorms
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometric_of_same_norms : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L L' : HermLB V.p) (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ), Norms V L f a l → Norms V L' f a l → L.Isometric L' := by
  first | exact @GlobalTheory.CoverNorm.Isom.isometric_of_norms | exact GlobalTheory.CoverNorm.Isom.isometric_of_norms | (intros; apply GlobalTheory.CoverNorm.Isom.isometric_of_norms <;> assumption)
