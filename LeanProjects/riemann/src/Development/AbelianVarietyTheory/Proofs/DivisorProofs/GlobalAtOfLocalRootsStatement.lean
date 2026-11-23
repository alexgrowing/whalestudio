import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalAtOfLocalRoots
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_at_of_local_roots : ∀ (D : D7) (Y : ShimX D.what₂.Tau) (p : ℕ) [Fact p.Prime] (ι : Type) [Fintype ι] (w : ι → ℝ) (jc : ι → (KW p →+* ℂ)) (M : ∀ la, DV.Mdl D p Y.N (rkOf (PsiOf D (jc la)) Y.N Y.j)) (rt : ∀ la, Bool × Rt D.what₂.Tau Y.N → (M la).Z.LB), UnramE D p → Term Y p w jc M rt → (∀ la, Roots (jc la) (M la) (rt la) ∧ Comm (M la) ∧ Cons (M la) (rt la) Y.chern ∧ Local (M la)) → GlobAt Y p := by
  first | exact @GlobalTheory.MixedGlobalChern.globAt_of_local | exact GlobalTheory.MixedGlobalChern.globAt_of_local | (intros; apply GlobalTheory.MixedGlobalChern.globAt_of_local <;> assumption)
