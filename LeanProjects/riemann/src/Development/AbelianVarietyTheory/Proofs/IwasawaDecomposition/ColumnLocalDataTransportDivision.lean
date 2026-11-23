import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColsReTo0S
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.WitTr

open GlobalTheory.Mem.Db

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
variable (w : ColW B f T) (Z : w.Lt) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)

set_option maxHeartbeats 8000000 in

def nchTTr {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) :
    NchT w (setDivZ Z N h) Wt (nchTr (D := w.D Z) N h nch) :=
  { n with tp := { n.tp with }, tie := { n.tie with }, chrPsi := n.chrPsi }

set_option maxHeartbeats 8000000 in

def kerTr {Gt : GatTies (w.D Z)} {cmp : LatCmp (w.D Z)} {Gy : G.LatInst (w.D Z)} (k : KerFam (w.D Z) Gt cmp (w.tw Z) Gy) :
    KerFam (w.D (setDivZ Z N h)) (gatTr (D := w.D Z) N h Gt) (cmpTr (D := w.D Z) N h cmp) (w.tw (setDivZ Z N h))
      (latTr (D := w.D Z) N h Gy) :=
  fun u v g => { k u v g with }

set_option maxHeartbeats 8000000 in

def columnLocalDataTransportDivision (c : ColumnDataSplitPrimes K w Z)
    (hR : IsRecG K.s (w.D (setDivZ Z N h)) (gatTr (D := w.D Z) N h c.Gt) (cmpTr (D := w.D Z) N h c.cmp)
      (DivTr.herm0S (D := w.D Z) N h c.g.herm) (fun u => DivTr.forms0S (D := w.D Z) N h (c.g.forms u))) :
    ColumnDataSplitPrimes K w (setDivZ Z N h) :=
  { DivTr.colTTr w Z N h c.toColT with isRec := hR, om := c.om }

end GlobalTheory.Mem.Top.Bl.WitTr

end
