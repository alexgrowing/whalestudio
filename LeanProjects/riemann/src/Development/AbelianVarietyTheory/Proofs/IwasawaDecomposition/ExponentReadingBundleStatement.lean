import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentReadingBundle
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponent_reading_bundle : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP) (hE : GlobalTheory.PlugPt.HasExp N) (K : Ctx) (q : WPt (prmR N S Γ).s K) (c : ℝ) (b : Bundle (q.w.D q.Z) q.O c) (_ : BWit (p := prmR N S Γ) q b) (t : b.Comparison₂), GlobalTheory.PlugPt.pinPt (GlobalTheory.PlugPt.NRead.of RX hE (SXE S) (OX Γ)) K q c (b.part t).pt := by
  first | exact @GlobalTheory.PlugPt.pinPt_part_of_wit | exact GlobalTheory.PlugPt.pinPt_part_of_wit | (intros; apply GlobalTheory.PlugPt.pinPt_part_of_wit <;> assumption)
