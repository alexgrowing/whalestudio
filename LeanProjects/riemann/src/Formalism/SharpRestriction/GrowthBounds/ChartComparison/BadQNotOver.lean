import Formalism.SharpRestriction.GrowthBounds.ChartComparison.StepIn
import Formalism.LocalToGlobal.HermitianForms.TiedTwSym
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOneRec

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure LocPart (D : D7) {p : ℕ} (G : GAtP p) (Ch : Type) (n : ℕ) where
  cmpt : Ch → Type
  [fin : ∀ β, Fintype (cmpt β)]
  eC : (Σ β, cmpt β) ≃ G.comp
  loc : ∀ β, LocAt D.host.F D.host.E n (gatCh G fun a : cmpt β => eC ⟨β, a⟩)
  pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ D.what₂.Tau

attribute [instance] LocPart.fin

variable {D : D7} {Tw : TwForms D} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}
  {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
  {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)}

set_option maxHeartbeats 4000000 in

def stepInTw (W : TwFormsTiedS D Tw T J F) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) (i : ℕ) (h1 : 1 ≤ i)
    (hm : i ≤ D.R.m) {p : ℕ} (G : GAtP p) (dt : ∀ β, DetTie (W.ch u μ hμ i h1 hm β).lev)
    (L : LocPart D G (T.Ch u μ i) (D.R.N i)) : StepIn (Tw.fm u μ) i hm G where
  T := (D.mem u).A.T
  bad := badQ D (T.Q μ)
  eY := twYS T F u μ i hm
  okW := okQ D (T.Q μ)
  Ch := T.Ch u μ i
  chOf := T.chOf u μ i
  lat := fun c => latCrd D i hm (T.lat u μ i c)
  K := W.ch u μ hμ i h1 hm
  val := W.val u μ hμ i h1 hm
  tw := fun β => DetTw.ofChiD (dt β) (cTw D i)
  cmpt := L.cmpt
  eC := L.eC
  loc := L.loc
  pos := L.pos

theorem badQ_notOver (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (Q : Finset (HeightOneSpectrum (𝓞 D.host.F))) (hQ : okQ D Q w) (w' : HeightOneSpectrum (𝓞 D.host.F)) (hw : w' ∈ badQ D Q) :
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal := by
  rcases hw with h | h
  · exact bad_notOver u w hg w' h
  · exact hQ w' h

end Formalism.MainNotions.G.CmpJ

end
