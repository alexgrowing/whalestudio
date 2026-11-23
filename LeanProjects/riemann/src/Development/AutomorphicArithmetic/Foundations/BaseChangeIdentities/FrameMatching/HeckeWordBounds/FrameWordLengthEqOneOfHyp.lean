import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.HeckeLevelWordBase

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2

namespace UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem frameWord_length_eq_one_of_hyp (h : LocWord) : heckeLevelWordBase := by
  intro E _ _ _ n d hd a ha p
  exact (h E n d hd a ha [Sum.inl ()] 0 (by simp)).1 p

theorem wordId_of (h1 : TestWord) (h2 : TraceWord) : WordId := by
  intro hR E _ _ _ hE n _ π S T F₀ F hS
  choose c₀ hc₀ hc using h1 hR E n π S T F₀ F hE hS
  exact ⟨fun i => F₀.C.c i * (F.B i).vol, c₀, hc₀, fun ws hws => ⟨fun i => hc i ws hws, h2 hR E n π S T F₀ F hE hS ws hws⟩⟩

end UpperTheory.BaseChangeIdentities.FrameWordIdentity

end
