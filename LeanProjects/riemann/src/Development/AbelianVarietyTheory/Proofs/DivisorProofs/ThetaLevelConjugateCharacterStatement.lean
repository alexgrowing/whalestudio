import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLevelConjugateCharacter
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealPins3RealTOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealPinsRealTOf
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_level_conjugate_character : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : GlobalTheory.Fc.Bundle (q.w.D q.Z) q.O c) (w : BWit q b), q.O.L.sc = K.s → w.y.y.tS ∈ Formalism.L2.Theta.GfC (Yc (q.w.D q.Z) 0) ∧ Formalism.IndefR.AutomorphicEvaluation.ConjLevel w.y.y.tS⁻¹ (levS _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 true))) (Formalism.IndefR.Lev.levChi _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 true))) (w.y.y.ιS ⁻¹' seeKS b.S.X) (fun k => seeChiS b.S.X (w.y.y.ιS k)) ∧ Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt w.x.R.toRealDat w.x.F.lv2 b.S.X w.y.y.instEq w.y.y.tS := by
  first | exact @GlobalTheory.Mem.R3.LinkLev.tS_fin_conj_match | exact GlobalTheory.Mem.R3.LinkLev.tS_fin_conj_match | (intros; apply GlobalTheory.Mem.R3.LinkLev.tS_fin_conj_match <;> assumption)
