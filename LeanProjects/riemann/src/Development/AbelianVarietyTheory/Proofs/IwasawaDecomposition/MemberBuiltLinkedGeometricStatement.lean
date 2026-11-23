import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberBuiltLinkedGeometric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultW
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.member_built_linked_geometric : HypA → HypE → HypH → ExistsUnlocalizedSaturatedState → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, HypN hL → ∀ cDep : ℝ, MultQ (prmR (NEo hL cDep) SExt.none (geoCl anyGeometry)) → MemberE (prmR (NEo hL cDep) SExt.none (geoCl anyGeometry)).s ∧ GlobalTheory.Fc.ExBL KPx (IsBuiltE (prmR (NEo hL cDep) SExt.none (geoCl anyGeometry)).s) (IsGoodE (prmR (NEo hL cDep) SExt.none (geoCl anyGeometry)).s) (IsLinked (prmR (NEo hL cDep) SExt.none (geoCl anyGeometry))) := by
  first | exact @GlobalTheory.Mem.Top.Bl.memberE_exBL_prm1 | exact GlobalTheory.Mem.Top.Bl.memberE_exBL_prm1 | (intros; apply GlobalTheory.Mem.Top.Bl.memberE_exBL_prm1 <;> assumption)
