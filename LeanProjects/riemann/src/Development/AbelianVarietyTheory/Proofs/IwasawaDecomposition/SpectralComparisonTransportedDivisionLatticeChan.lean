import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RelabelledWeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReOfDiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinXSpectralRedivisionFullChoices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultREqReL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvEvHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvRowJ
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports

noncomputable section

open GlobalTheory.Mem.R3.Tr Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe

theorem of_heq_cast {α β : Sort _} {y : β} {x : α} (P : α → Prop) (h : HEq y x) (hx : P x) :
    P (cast (type_eq_of_heq h) y) := by
  cases h
  exact hx

set_option maxHeartbeats 4000000 in

theorem sAtL_exists_ofDiv : ∀ (B : Base) (C : Cols B) (a : Late B C) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] (R : RealDat a.D A Ks) (F : Face a.D A) (F0 : ∀ u, Forms0 a.D u) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (s : SAt R F eE F0) (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ) (F₁ : ∀ u, Forms0 (reL a (New.ofDiv a.D N hh)).D u), SameL a (New.ofDiv a.D N hh) F0 F₁ → ∃ s' : SAtL a (New.ofDiv a.D N hh) R F eE F₁, SAtL.pt a (New.ofDiv a.D N hh) s' = tL a (New.ofDiv a.D N hh) s.t := by
  intro B C a G' _ _ Pl0 T A Ks _ _ iK R F F0 eE s N hh F₁ hS
  have hF : FinX (reY (New.ofDiv a.D N hh) s.P.Y) := finX_reY a.D (New.ofDiv a.D N hh) s.P.X s.P.Y s.P.fin
  have h : SameForms0LevelsAndValues (New.ofDiv a.D N hh) F0 ((by with_unfolding_all exact (F₁ :))) := hS
  obtain ⟨S', hj⟩ := SRest.exists_re_ofDiv N hh s.S h hF
  have hsee := mvSee a (New.ofDiv a.D N hh) R F s.P.X s.P.inst s.t s.see
  have hev := mvEv_holds a (New.ofDiv a.D N hh) R F s.P.X s.P.inst s.P.G s.t s.c s.ev
  have hrow := mvRowJ a (New.ofDiv a.D N hh) R s.P.X s.P.inst s.P.G s.t eE s.S.j s.rowJ
  letI := alg (reL a (New.ofDiv a.D N hh)) iK
  have hrow' := of_heq_cast (fun j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC s.P.X s.P.G =>
      RowJ (real (reL a (New.ofDiv a.D N hh)) R) (eL a (New.ofDiv a.D N hh) R eE) (XL a (New.ofDiv a.D N hh) s.P.X)
        (hL a (New.ofDiv a.D N hh) s.P.inst) (gdL a (New.ofDiv a.D N hh) s.P.G) (tL a (New.ofDiv a.D N hh) s.t)
        (jL a (New.ofDiv a.D N hh) j)) hj hrow
  let s' : SAt (real (reL a (New.ofDiv a.D N hh)) R) (face (reL a (New.ofDiv a.D N hh)) F) (eL a (New.ofDiv a.D N hh) R eE) F₁ :=
    { P := (by with_unfolding_all exact (s.P.re (New.ofDiv a.D N hh) h hF :))
      S := (by with_unfolding_all exact (S' :))
      t := tL a (New.ofDiv a.D N hh) s.t
      c := s.c
      c_pos := s.c_pos
      see := (by with_unfolding_all exact (hsee :))
      ev := (by with_unfolding_all exact (hev :))
      rowJ := (by with_unfolding_all exact (hrow' :)) }
  exact ⟨s', (by with_unfolding_all exact (Eq.refl (tL a (New.ofDiv a.D N hh) s.t) :))⟩

end GlobalTheory.Mem.SRe

end
