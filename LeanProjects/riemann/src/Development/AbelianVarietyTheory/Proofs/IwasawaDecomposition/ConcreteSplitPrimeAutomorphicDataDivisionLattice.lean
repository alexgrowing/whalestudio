import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLocalDataTransportDivision
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Top.Bl.WitTr
open Formalism.MainNotions.G Formalism.UG Formalism.L2.Forms Formalism.L2.G
attribute [local instance] Formalism.BasicNotions.factResChar

section Gen

variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) {X : Formalism.L2.Herm.Herm0 D}

set_option maxHeartbeats 2000000 in

def cmpInS (I : Cmp.CmpIn D X) : Cmp.CmpIn (setDiv D N h) (DivTr.herm0S N h X) := { I with }

set_option maxHeartbeats 2000000 in

theorem cmpHyp0P_setDiv {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : Cmp.CmpIn D X} (H : CmpHyp0P T Gt I) :
    CmpHyp0P (D := setDiv D N h) (fun u => DivTr.forms0S N h (T u)) (gatTr N h Gt) (cmpInS N h I) :=
  ⟨H.ex, H.evInj, H.ptEx, H.ptAll, H.chi, H.latM⟩

theorem stdB_setDiv {B : GL (Fin D.R.k) D.host.E} (hB : Cmp.StdB D B) : Cmp.StdB (setDiv D N h) B := hB

set_option maxHeartbeats 2000000 in

theorem cmpHyp_setDiv {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : Cmp.CmpIn D X} (H : Cmp.CmpHyp T Gt I) :
    Cmp.CmpHyp (D := setDiv D N h) (fun u => DivTr.forms0S N h (T u)) (gatTr N h Gt) (cmpInS N h I) :=
  ⟨H.ex, H.uniq, H.pos, H.chi, H.li, H.latM⟩

set_option maxHeartbeats 2000000 in

theorem latCmpC_setDiv {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : Cmp.CmpIn D X} (H : Cmp.CmpHyp T Gt I) :
    cmpTr N h (Cmp.latCmpC T Gt I H) =
      Cmp.latCmpC (D := setDiv D N h) (fun u => DivTr.forms0S N h (T u)) (gatTr N h Gt) (cmpInS N h I) (cmpHyp_setDiv N h H) := rfl

set_option maxHeartbeats 2000000 in

theorem sigma_setDiv {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : Cmp.CmpIn D X} (H : Cmp.CmpHyp T Gt I)
    (H0 : Formalism.L2.Herm.Herm0 D) :
    (⟨setDiv D N h, gatTr N h Gt, cmpTr N h (Cmp.latCmpC T Gt I H), DivTr.herm0S N h H0, fun u => DivTr.forms0S N h (T u)⟩ :
      Σ D : D7, GatTies D × LatCmp D × Formalism.L2.Herm.Herm0 D × ∀ u, Forms0 D u) =
    ⟨setDiv D N h, gatTr N h Gt,
      Cmp.latCmpC (D := setDiv D N h) (fun u => DivTr.forms0S N h (T u)) (gatTr N h Gt) (cmpInS N h I) (cmpHyp_setDiv N h H),
      DivTr.herm0S N h H0, fun u => DivTr.forms0S N h (T u)⟩ := by
  rw [latCmpC_setDiv]

end Gen

attribute [local instance_reducible] tauRec hP frobSet lamRec packC locPackC recG gatTiesG extRec embRec cmpInC hermitianLevelZeroOfRecursion levTieG gatRecP_lev gatRec_lev gatRec_pos
  DivTr.herm0S DivTr.forms0S DivTr.atTTS cmpInS LocPack.posOK

set_option maxHeartbeats 1600000 in

theorem isRecG_setDiv : ∀ (sc : Scale) (D : D7) (Gt : GatTies D) (c : LatCmp D) (H : Formalism.L2.Herm.Herm0 D)
    (F : ∀ u, Formalism.L2.Forms.Forms0 D u) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ),
    IsRecG sc D Gt c H F → IsRecG sc (setDiv D N h) (gatTr N h Gt) (cmpTr N h c) (DivTr.herm0S N h H)
      (fun u => DivTr.forms0S N h (F u)) := by
  intro sc D Gt c H F N h hR
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, eq⟩ := hR
  cases eq
  refine IsRecG.intro (setDiv D0 N h) Lc I ?a1 ?a2 ?a3 ?a4 ?a5 B ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 ?a13
  case a1 => with_reducible_and_instances exact ψ
  case a2 => with_reducible_and_instances exact hd
  case a3 => with_reducible_and_instances exact DivTr.herm0S N h H0
  case a4 => with_reducible_and_instances exact hL
  case a5 => with_reducible_and_instances exact fun u => DivTr.forms0S N h (T u)
  case a6 => with_reducible_and_instances exact stdB_setDiv N h hBs
  case a7 => with_reducible_and_instances exact hB
  case a8 => with_reducible_and_instances exact iK
  case a9 => with_reducible_and_instances exact lam
  case a10 => with_reducible_and_instances exact hK
  case a11 => with_reducible_and_instances exact hPos
  case a12 => with_reducible_and_instances exact cmpHyp0P_setDiv N h CH
  case a13 =>
    with_reducible_and_instances refine Eq.trans (sigma_setDiv N h _ H0) ?_
    with_reducible_and_instances exact Eq.refl _

end GlobalTheory.Mem.Top.Bl.WitTr
end
