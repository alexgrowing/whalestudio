import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsUnitRescaling
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norms_unit_rescaling : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L : HermLB V.p) (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) (c : Y.X → Y.Fn), (∀ x, UnitAt x (c x)) → Norms V L f a l → Norms V L (fun x => c x * f x) (fun σ y => Real.log ‖ratVal (c (under y)) y‖ + a σ y) (fun v e y => Real.log (e.w (valAt y.1 (c (below y.1)))) + l v e y) := by
  first | exact @GlobalTheory.CoverNorm.norms_mul_unit | exact GlobalTheory.CoverNorm.norms_mul_unit | (intros; apply GlobalTheory.CoverNorm.norms_mul_unit <;> assumption)
