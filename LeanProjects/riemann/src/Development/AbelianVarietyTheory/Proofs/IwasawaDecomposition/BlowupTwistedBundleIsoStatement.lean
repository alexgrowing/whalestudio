import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupTwistedBundleIso
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blowup_twisted_bundle_iso : ∀ {X Z : Scheme.{0}} (π : Z ⟶ X) (ΩX : LB X) (ΩZ : LB Z) (DX : GlobalTheory.EffCartierData X) (EX : GlobalTheory.EffCartierData Z) (h : DX.KeepsRegular π) (k T : ℕ), ΩX.IsLB → ΩZ.IsLB → LBIso ΩZ (ΩX.pull π) → (GlobalTheory.CechPic.tens (lbPow ΩZ (T * k)) (GlobalTheory.CechPic.dual (((DX.pull π h).nsmul T).add EX).lb)).IsLB ∧ LBIso (GlobalTheory.CechPic.tens (lbPow ΩZ (T * k)) (GlobalTheory.CechPic.dual (((DX.pull π h).nsmul T).add EX).lb)) (GlobalTheory.CechPic.tens (lbPow ((GlobalTheory.CechPic.tens (lbPow ΩX k) (GlobalTheory.CechPic.dual DX.lb)).pull π) T) (GlobalTheory.CechPic.dual EX.lb)) := by
  first | exact @GlobalTheory.PolClass.lbIso_blowPol | exact GlobalTheory.PolClass.lbIso_blowPol | (intros; apply GlobalTheory.PolClass.lbIso_blowPol <;> assumption)
