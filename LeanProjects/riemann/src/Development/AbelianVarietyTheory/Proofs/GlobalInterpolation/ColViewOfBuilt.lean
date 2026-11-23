import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes

noncomputable section

namespace GlobalTheory.Fc.Cv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem colView_of_built {𝒮 : GlobalTheory.Mem.Top.Bl.Slots} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
    {c : V4.Core K (w.st Z) f T} (b : GlobalTheory.Mem.Top.Bl.Built 𝒮 K w Z c) : ColView w Z c.O.tw c.O.nch where
  jets := b.pin.jets
  rowInt := b.what₂.rowInt
  tw_eq := congrArg (fun s => s.2.2.1) b.ker_eq
  tup := ⟨b.n.tp, b.n.xi⟩

theorem overCols_built : ∀ 𝒮 : Slots, OverCols (IsBuilt 𝒮) ∧ ∀ P : CP, (∀ K B f T w Z c, P K B f T w Z c → BuiltC 𝒮 K B f T w Z c) →
    OverCols (positionOf P) := by
  intro 𝒮
  have key : ∀ P : CP, (∀ K B f T w Z c, P K B f T w Z c → BuiltC 𝒮 K B f T w Z c) → OverCols (positionOf P) :=
    fun P hP K X f T c hc =>
      positionOf_mono (fun K B f T w Z c h => let ⟨b⟩ := hP K B f T w Z c h; colView_of_built b) K X f T c hc
  exact ⟨key (BuiltC 𝒮) fun _ _ _ _ _ _ _ h => h, key⟩

end GlobalTheory.Fc.Cv

end
