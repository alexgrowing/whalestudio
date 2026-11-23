import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

namespace GlobalTheory.HeightCounting.SerMove.Ids

theorem coeffF_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {l' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H'}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l'}
    (hH : H' = H) (hl : HEq l' l) (hc : HEq c' c) : c'.F = c.F := by
  subst hH
  obtain rfl := eq_of_heq hl
  obtain rfl := eq_of_heq hc
  rfl

theorem gc_equiv {B B' : Base} {px : PreX B.toPre} {px' : PreX B'.toPre} (h : Enl B B') (hp : HEq px' px) :
    ∃ γ : GlobalTheory.Mem.R3.Gc B px ≃* GlobalTheory.Mem.R3.Gc B' px', ∀ u, HEq (γ u) u := by
  obtain ⟨e, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at e
  subst e
  cases hp
  exact ⟨MulEquiv.refl _, fun _ => HEq.rfl⟩

theorem dat_F_eq {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok}
    {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl} {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'}
    (h : Enl B B') (e : ExtN z z') : z'.core.Q.c.F = z.core.Q.c.F := by
  have hH := e.H
  have hl := e.l
  have hc := e.c
  clear e
  obtain ⟨e0, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at e0
  subst e0
  exact coeffF_eq (eq_of_heq hH) hl hc

theorem field_group_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∃ (eK : ↥(sideAt x g hg a).core.Q.c.F ≃+* ↥(sideAt x' g' hg' a').core.Q.c.F) (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ y, ((eK y : ↥(sideAt x' g' hg' a').core.Q.c.F) : ℂ) = (y : ℂ)) ∧ ∀ u, HEq (γ u) u := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a'
  have hc := l.extN.c
  have hH := l.extN.H
  have hl := l.extN.l
  show ∃ (eK : x.m.z.core.Q.c.F ≃+* x'.m.z.core.Q.c.F) (γ : GlobalTheory.Mem.R3.Gc B w.px ≃* GlobalTheory.Mem.R3.Gc B' w'.px), _
  obtain ⟨γ, hγ⟩ := gc_equiv l.enl l.px
  have hF : x'.m.z.core.Q.c.F = x.m.z.core.Q.c.F := dat_F_eq (z := datAt x g) (z' := datAt x' g') l.enl l.extN
  exact ⟨(IntermediateField.equivOfEq hF.symm).toRingEquiv, γ, fun y => rfl, hγ⟩

end GlobalTheory.HeightCounting.SerMove.Ids
