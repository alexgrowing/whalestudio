import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingOkClassAtPlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisting_ok_class_at_place : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (ch : NChoice (Dof x)) (tp : TupTied (Dof x) (cfOf x) ch), tp.xi = w.I.xi → tp.psi = T.psi → ch.Q = QOf P → (∀ v, TwistedAt (Dof x) v → ch.k' v = T.k v) → ChoiceSide (Dof x) (cfOf x) l.mt.M l.b.Bs.exp ch tp → ∀ v, TwistedAt (Dof x) v → IntegralHeckeForms.TwOK (ch.twI v) (ch.k' v) (ch.Q v) (GlobalTheory.PlaceRead.chr ch v) →
  IntegralHeckeForms.ClsQ (D := Dof x) (ch.Q v) ∧ ∀ (j : Fin (Dof x).R.m) (ι : GlobalTheory.PlaceRead.KE ch v →+* ℂ), (∀ y, ι (ch.embW v y) = (Dof x).what₂.embLL y) →
    GlobalTheory.ConjTwist.IsTupOf x.m.z.R.toRealDat (l.b.ser.ex.ρ.B (ch.twI v) j (ch.sd v)) (GlobalTheory.PlaceRead.twVia l.b.ser.ex.ρ ι) (x.r.Y.tupT ((Dof x).what₂.muTw v)) := by
  first | exact @GlobalTheory.PlaceRead.TupAt.isTupOf_tupT_muTw_of_embW_eq | exact GlobalTheory.PlaceRead.TupAt.isTupOf_tupT_muTw_of_embW_eq | (intros; apply GlobalTheory.PlaceRead.TupAt.isTupOf_tupT_muTw_of_embW_eq <;> assumption)
