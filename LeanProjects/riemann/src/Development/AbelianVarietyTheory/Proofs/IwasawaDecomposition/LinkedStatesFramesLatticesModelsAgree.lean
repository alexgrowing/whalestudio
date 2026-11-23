import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.SerMove.FrameValuesAtLevel
variable {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'}

set_option maxHeartbeats 4000000 in

theorem ΛV_at (q : B'.toPre = B.toPre) (hx : ExtN z z') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    HEq (z.R.ΛV i) (z'.R.ΛV i') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  exact heq_of_eq (congrFun (eq_of_heq hx.ΛV) i).symm

set_option maxHeartbeats 4000000 in

theorem ΛW_at (q : B'.toPre = B.toPre) (hx : ExtN z z') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    HEq (z.R.ΛW i) (z'.R.ΛW i') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  exact heq_of_eq (congrFun (eq_of_heq hx.ΛW) i).symm

set_option maxHeartbeats 4000000 in

theorem βV_at (q : B'.toPre = B.toPre) (hx : ExtN z z') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    HEq (z.R.βV i) (z'.R.βV i') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  exact heq_of_eq (congrFun (eq_of_heq hx.βV) i).symm

set_option maxHeartbeats 4000000 in

theorem βW_at (q : B'.toPre = B.toPre) (hx : ExtN z z') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    HEq (z.R.βW i) (z'.R.βW i') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  exact heq_of_eq (congrFun (eq_of_heq hx.βW) i).symm

set_option maxHeartbeats 4000000 in

theorem sameVec_gen (q : B'.toPre = B.toPre) (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    {S : (w.st Z).toD7.what₂.Tau → Formalism.BasicNotions.TH.SPar} {S' : (w'.st Z').toD7.what₂.Tau → Formalism.BasicNotions.TH.SPar}
    (M : Formalism.IndefR.Mult.DSModel (Formalism.IndefR.Links.Wc (w.st Z).toD7 i) S) (M' : Formalism.IndefR.Mult.DSModel (Formalism.IndefR.Links.Wc (w'.st Z').toD7 i') S')
    (a : HEq M'.H M.H) (b : HEq M'.nacg M.nacg) (c : HEq M'.ips M.ips) (d : HEq M'.σ M.σ) (g : HEq M'.fr M.fr)
    (v : M.Vec) (v' : M'.Vec) (hv : HEq v' v) : GlobalTheory.TwInputs.Move.SameVec v v' := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  cases M
  cases M'
  dsimp only at a b c d g
  cases a; cases b; cases c; cases d; cases g
  intro τ τ' hτ
  cases hτ
  have e := eq_of_heq hv
  subst e
  rfl

set_option maxHeartbeats 4000000 in

theorem v₀_of_extN (q : B'.toPre = B.toPre) (hx : ExtN z z') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    GlobalTheory.TwInputs.Move.SameVec (z.geo.v₀ i (w.st Z).toD7.what₂.embLL) (z'.geo.v₀ i' (w'.st Z').toD7.what₂.embLL) :=
  have h := hx.MW i i' hi
  sameVec_gen q i i' hi _ _ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.2.2.1 _ _ h.2.2.2.2.2.2.2.2.2.1

end GlobalTheory.HeightCounting.SerMove.FrameValuesAtLevel

namespace GlobalTheory.HeightCounting.SerMove

set_option maxHeartbeats 4000000 in

theorem frames_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), Frames (sideAt x g hg a) (sideAt x' g' hg' a') := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a'
  have q : B'.toPre = B.toPre := l.enl.1
  have hx := l.extN
  refine ⟨hx.Pg.symm, hx.ψ.symm, hx.θ.symm, fun j j' h => FrameValuesAtLevel.ΛV_at q hx j j' h, fun j j' h => FrameValuesAtLevel.ΛW_at q hx j j' h,
    fun j j' h => FrameValuesAtLevel.βV_at q hx j j' h, fun j j' h => FrameValuesAtLevel.βW_at q hx j j' h,
    fun j j' h => ((hx.BV j j' h).2.2.2.2.2).symm, fun j j' h => ((hx.BV j j' h).2.2.1).symm, fun j j' h => ?_, fun j j' h => ?_⟩
  · show GlobalTheory.TwInputs.Move.SameModel (x.m.z.R.MW j (Formalism.IndefR.Links.sg0 (Dof x) (sideAt x g hg a).A3.A)) (x'.m.z.R.MW j' (Formalism.IndefR.Links.sg0 (Dof x') (sideAt x' g' hg' a').A3.A))
    rw [GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x g hg a), GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x' g' hg' a')]
    have m := hx.MW j j' h
    exact ⟨m.1.symm, m.2.1.symm, m.2.2.1.symm, m.2.2.2.1.symm, m.2.2.2.2.1.symm, m.2.2.2.2.2.1.symm, m.2.2.2.2.2.2.1.symm⟩
  · show GlobalTheory.TwInputs.Move.SameVec (g.v₀ j (Formalism.IndefR.Links.sg0 (Dof x) (sideAt x g hg a).A3.A)) (g'.v₀ j' (Formalism.IndefR.Links.sg0 (Dof x') (sideAt x' g' hg' a').A3.A))
    rw [GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x g hg a), GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x' g' hg' a')]
    exact FrameValuesAtLevel.v₀_of_extN q hx j j' h

end GlobalTheory.HeightCounting.SerMove
