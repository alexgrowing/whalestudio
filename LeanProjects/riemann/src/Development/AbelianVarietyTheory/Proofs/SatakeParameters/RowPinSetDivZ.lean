import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Col2 NumberField

set_option maxHeartbeats 1000000

namespace GlobalTheory.AtG

theorem rowPin_setDivZ : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (ht : B.Word → ℝ) (a : (I.rec7 l Z).what₂.Tup), GlobalTheory.AtG.RowPin I h l Z a → GlobalTheory.AtG.RowPin I h l (GlobalTheory.Mem.Db.setDivZ Z N ht) a := by
  intro B X I h l Z N ht a hp
  exact hp

end GlobalTheory.AtG
