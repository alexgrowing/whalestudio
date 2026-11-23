import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnfoldingIdentityMatchedFamilyClosedTerms
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs Formalism.FourierDecayAlt GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_identity_matched_family_closed_terms : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl), ClsRow TS cls → (∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ FP : ∀ p : PlF D, LocNG.FPair (locH (zOf Y) p) D.R.rS, Based (zOf Y) FP (Tu D u) (Tu D u') F F' → LocClosed F F' (zOf Y) FP TS) → ∀ (γ : PN.Pts D.host.E D.R.rS) (Fm : LocFam (zOf Y) Cl (NuC D)), FamTie TS cls (nmlOf Y u u') γ Fm → ∃ V0, OrbitFamilyIdentityAt Fm V0 := by
  first | exact @GlobalTheory.Unfold.Tied.unfold_tied | exact GlobalTheory.Unfold.Tied.unfold_tied | (intros; apply GlobalTheory.Unfold.Tied.unfold_tied <;> assumption)
