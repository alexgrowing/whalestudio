import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorNormPullbackComponent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_norm_pullback_component : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (C : Closeds (gen s.T.Z : Scheme.{0})) (n : CxPts (genStr s.T.Z) (embOf κ.e σ) → ℝ), Smooth (Φ.C k).π → IsDivNorm (manifold s.T.Z (embOf κ.e σ)) C n → IsDivNorm ((Φ.C k).Y.an σ) (C.preimage (Φ.C k).π.continuous) (fun z => n ((Φ.C k).down z)) := by
  first | exact @GlobalTheory.DivPullback.isDivNorm_flag | exact GlobalTheory.DivPullback.isDivNorm_flag | (intros; apply GlobalTheory.DivPullback.isDivNorm_flag <;> assumption)
