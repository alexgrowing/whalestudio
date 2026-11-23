import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeightSmoothNormalization
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_weight_smooth_normalization : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y), Norms V (HermLB.triv V.p) (fun _ => 1) (fun _ _ => 0) (fun _ _ _ => 0) ∧ ∀ (u : ∀ σ : 𝓞 F →+* ℂ, CxPts V.p σ → ℝ) (hu : ∀ σ y, CxPts.CInfAt (u σ) y) (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ), (∀ (σ : F →+* ℂ) (z : CxPts (V.π ≫ Y.str) σ) (y : Pts Y σ) (y' : CxPts V.p (σ.comp (algebraMap (𝓞 F) F))), y.1 = z.1 ≫ V.π → y'.1 = z.1 ≫ V.j → a σ y = -(u _ y' / 2)) → Norms V (ArInt.fnB u hu hc) (fun _ => 1) a (fun _ _ _ => 0) := by
  first | exact @GlobalTheory.CoverNorm.norms_triv_fnB | exact GlobalTheory.CoverNorm.norms_triv_fnB | (intros; apply GlobalTheory.CoverNorm.norms_triv_fnB <;> assumption)
