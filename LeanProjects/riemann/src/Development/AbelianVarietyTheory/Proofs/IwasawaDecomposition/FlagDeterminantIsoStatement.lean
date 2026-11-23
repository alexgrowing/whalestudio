import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDeterminantIso
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_determinant_iso : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp), LBIso ((Φ.C k).Y.lb (-∑ x : Letter S.Dw, (Φ.C k).gr x.1 x.2)) ((FlagMod.detOm s.T.Z).pull ((Φ.C k).π ≫ genι s.T.Z)) := by
  first | exact @GlobalTheory.ShFam.lbIso_detOm_flag | exact GlobalTheory.ShFam.lbIso_detOm_flag | (intros; apply GlobalTheory.ShFam.lbIso_detOm_flag <;> assumption)
