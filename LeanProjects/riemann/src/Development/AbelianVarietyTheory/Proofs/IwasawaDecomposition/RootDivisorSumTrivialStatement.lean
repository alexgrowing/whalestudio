import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootDivisorSumTrivial
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatSectionIsFlatStatement
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_divisor_sum_trivial : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (τ : D.what₂.Tau), toPic (∑ i : Fin N, divOf (Φ.C k) (rootExp S (τ, i))) = 0 := by
  first | exact @GlobalTheory.ShFam.toPic_sum_divOf_rootExp | exact GlobalTheory.ShFam.toPic_sum_divOf_rootExp | (intros; apply GlobalTheory.ShFam.toPic_sum_divOf_rootExp <;> assumption)
