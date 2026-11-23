import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.YvRatOfValRat

open Formalism.MainNotions.G Formalism.BasicNotions NumberField

noncomputable section

namespace Formalism.L2.G.Cmp

section Rat

variable {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

theorem li_step (j : ℕ) (f : ((Tw.fm u (D.what₂.muAt w)).lat j).V →ₛₗ[c.embW u w h] Lv.Fm j)
    (hinj : Function.Injective f)
    (hrat : ∀ x, RatFnP (Fl.Pj j) (Lv.comp j) (c.embW u w h) (f x)) :
    LinearIndependent (D.gat u w h).Kf fun a => f (((Tw.fm u (D.what₂.muAt w)).lat j).b a) := by
  refine li_of_rat (e := c.embW u w h) (ev := evP (P := Fl.Pj j) (α := Lv.comp j)) (cmp := f.toAddMonoidHom)
    ?_ (fun a x => f.map_smulₛₗ a x) ?_ hinj _
    ((Tw.fm u (D.what₂.muAt w)).lat j).b.linearIndependent
  · intro F hF
    funext a L
    ext m
    simpa [evP] using hF (a, L, m)
  · intro x t
    obtain ⟨Q, hQ⟩ := hrat x t.1 t.2.1
    exact ⟨Q.coeff t.2.2, by simp [evP, ← hQ, MvPolynomial.coeff_map]⟩

def CmpUp.ofRat (cmpS : ∀ j, ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V →ₛₗ[c.embW u w h] Lv.Fm (j + 1))
    (injS : ∀ j, j + 1 ≤ D.R.m → Function.Injective (cmpS j))
    (ratS : ∀ j, j + 1 ≤ D.R.m → ∀ x, RatFnP (Fl.Pj (j + 1)) (Lv.comp (j + 1)) (c.embW u w h) (cmpS j x)) :
    CmpUp c Tw u w h Lv where
  cmpS := cmpS
  liS := fun j hj => li_step (j + 1) (cmpS j) (injS j hj) (ratS j hj)

end Rat

section Forced

variable {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

variable [Fact (D.what₂.places.resChar w).Prime] {Gt : GatTies D} {Ch : Chain Lv}

end Forced

end Formalism.L2.G.Cmp

end
