import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumDivisorAll
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_sum_divisor_all : GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (GlobalTheory.HeightCounting.Up.NEb hL K B f T w Z Wt p0 t nch n xd c)) → RL.At (prmR N S Γ) R1.DivisorConditionAtBundlePoints → RL.At (prmR N S Γ) fun Q L => Row Q L (AtAll fun D O c (b : Bundle D O c) => ∀ t : b.Comparison₂, Ind.PIota D O c (b.part t) ∧ GlobalTheory.ExportPin.ClassSumPin (b.part t).pt ∧ (b.part t).pt.Ties ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt) := by
  first | exact @GlobalTheory.GeoTies.linked_ties | exact GlobalTheory.GeoTies.linked_ties | (intros; apply GlobalTheory.GeoTies.linked_ties <;> assumption)
