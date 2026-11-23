import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRootDivisorRelation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_root_divisor_relation : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp), (∑ x : DV.Rt D.what₂.Tau N, (if (x.2 : ℕ) < j then 0 else 2 : ℤ) • divOf (Φ.C k) (rootExp S x)) = -(∑ x : Letter S.Dw, (Φ.C k).gr x.1 x.2) + ∑ x : DV.Rt D.what₂.Tau N, divOf (Φ.C k) (rootExp S x) := by
  first | exact @GlobalTheory.RootSum.sum_two_roots_ge | exact GlobalTheory.RootSum.sum_two_roots_ge | (intros; apply GlobalTheory.RootSum.sum_two_roots_ge <;> assumption)
