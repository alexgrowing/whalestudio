import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColsReTo0S
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df GlobalTheory.Mem.Db NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Db.DivTr

section GyGen

variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)

@[reducible] def ledBack (L : SizeData₂ (setDiv D N h)) : SizeData₂ D := { L with }

@[reducible] def instBack {L : SizeData₂ (setDiv D N h)} (X : G.Inst (setDiv D N h) L) : G.Inst D (ledBack N h L) := { X with }

end GyGen

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}
variable (w : ColW B f T) (Z : w.Lt) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)

def kerTr {t : ColT w Z} {Gy : G.LatInst (w.D Z)} (ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy) :
    KerFam (w.D (setDivZ Z N h)) (colTTr w Z N h t).Gt (colTTr w Z N h t).cmp (w.tw (setDivZ Z N h)) (latTr (D := w.D Z) N h Gy) :=
  fun u v g => { ker u v g with }

set_option maxHeartbeats 4000000 in

def ktTr {t : ColT w Z} {X : DivX (w.D Z)} {Gy : G.LatInst (w.D Z)} {ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy}
    (kt : KerT t X Gy ker) :
    KerT (colTTr w Z N h t) (divTr (D := w.D Z) N h X) (latTr (D := w.D Z) N h Gy) (kerTr w Z N h ker) :=
  { kt with
    O := fun u a => { kt.O u a with }
    E := { kt.E with }
    std := { kt.std with }
    ok := ⟨⟨fun u μ v hv => { (kt.ok.1.choose u μ v hv) with }, fun u μ v hv => kt.ok.1.choose_spec u μ v hv⟩, kt.ok.2⟩ }

set_option maxHeartbeats 8000000 in

theorem entC_tr {t : ColT w Z} {X : DivX (w.D Z)} {Gy : G.LatInst (w.D Z)} {ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy}
    (kt : KerT t X Gy ker)
    (H : ∃ (Pl : Examples₂.EntPl (w.D Z)) (Bs : Formalism.L2.Ker.PlaceMatrixFamily (w.D Z)) (hh : Formalism.L2.Ker.KerEntHyp Pl kt.O Bs X (w.tw Z)),
      kt.E = Formalism.L2.Ker.kerEntC Pl kt.O Bs hh) :
    ∃ (Pl : Examples₂.EntPl (w.D (setDivZ Z N h))) (Bs : Formalism.L2.Ker.PlaceMatrixFamily (w.D (setDivZ Z N h)))
      (hh : Formalism.L2.Ker.KerEntHyp Pl (ktTr w Z N h kt).O Bs (divTr (D := w.D Z) N h X) (w.tw (setDivZ Z N h))),
      (ktTr w Z N h kt).E = Formalism.L2.Ker.kerEntC Pl (ktTr w Z N h kt).O Bs hh := by
  obtain ⟨Pl, Bs, hh, e⟩ := H
  exact ⟨{ Pl with }, Bs, { hh with },
    congrArg (fun E => ({ E with } : Formalism.BasicNotions.KerEnt (w.D (setDivZ Z N h)) (divTr (D := w.D Z) N h X) (w.tw (setDivZ Z N h)))) e⟩

end GlobalTheory.Mem.Db.DivTr

end
