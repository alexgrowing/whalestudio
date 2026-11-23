import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinatesMatrixActionFreeModule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinates_matrix_action_free_module : ∀ (X : Scheme.{0}) (h : ℕ), ∃ μ : Matrix (Fin h) (Fin h) ℤ →+* End (freeModule X (Fin h)), ∀ (N : Matrix (Fin h) (Fin h) ℤ) (W : X.Opens) (s : Γ(freeModule X (Fin h), W)), GlobalTheory.LatGlue.coords X h W ((μ N : freeModule X (Fin h) ⟶ freeModule X (Fin h)).app W s) = mv (RingHom.id _) N (GlobalTheory.LatGlue.coords X h W s) := by
  first | exact @GlobalTheory.ChainDesc.FreeAct.exists_act | exact GlobalTheory.ChainDesc.FreeAct.exists_act | (intros; apply GlobalTheory.ChainDesc.FreeAct.exists_act <;> assumption)
