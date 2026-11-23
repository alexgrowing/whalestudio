import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianHodgeBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_hodge_bundle_iso : ∀ (S : Scheme.{0}) (E : SplitExt S) (G : Over S) [GrpObj G] (h : ℕ), IsSemiAbelian G → E.IsGt G → GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega E.B) h → GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega G) (h + Module.finrank ℤ E.X) ∧ LBIso (hodge G (h + Module.finrank ℤ E.X)) (hodge E.B h) := by
  first | exact @GlobalTheory.GtHodge.isVB_omega_and_lbIso_hodge | exact GlobalTheory.GtHodge.isVB_omega_and_lbIso_hodge | (intros; apply GlobalTheory.GtHodge.isVB_omega_and_lbIso_hodge <;> assumption)
