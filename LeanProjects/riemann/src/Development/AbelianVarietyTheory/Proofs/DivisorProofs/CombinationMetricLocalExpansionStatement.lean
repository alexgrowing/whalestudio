import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinationMetricLocalExpansion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLineBundleInduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MSmoothAndSemiPosIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetWeightIsCInfOfPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAdelicMetricDivisorRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtOfDivisorRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinedMetricLocalPotentialExists
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.combination_metric_local_expansion : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (Mb : Adl (cxSt F) Y) (ι : Type) [Fintype ι] (ρ : ι → Adl (cxSt F) Y) (t : ι → ℝ) (g : ∀ σ : F →+* ℂ, Pts Y σ → ℝ), GlobalTheory.Mean4O.IsComb Mb ρ t g → (∀ i σ, (cxSt F).mSmooth Y σ (ρ i).D ((ρ i).m σ)) → ∀ σ (z0 : Pts Y σ), ∃ (c K aM : ℝ) (a : ι → ℝ) (U fM : Y.Fn) (f : ι → Y.Fn), c ≠ 0 ∧ UnitAt (under z0) U ∧ Mb.D.GeneratesAt (under z0) fM ∧ (∀ i, (ρ i).D.GeneratesAt (under z0) (f i)) ∧ ∀ᶠ z in nhds z0, c * g σ z = Real.log (‖ratVal U z‖ ^ 2) + ∑ i, a i * lnN ((ρ i).m σ) (f i) z + aM * lnN (Mb.m σ) fM z + K := by
  first | exact @GlobalTheory.Mean4O.CombLocal.comb_local | exact GlobalTheory.Mean4O.CombLocal.comb_local | (intros; apply GlobalTheory.Mean4O.CombLocal.comb_local <;> assumption)
