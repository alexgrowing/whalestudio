import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pinned_local_groups_have_level : ∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) τ cG (G : ∀ PP : d.c.Pg, GAt d τ PP.1), d.Base → PinGBy G cG → ∀ PP, (G PP).Lev := by
  first | exact @GlobalTheory.LocMod.LevBack.lev_of_pin | exact GlobalTheory.LocMod.LevBack.lev_of_pin | (intros; apply GlobalTheory.LocMod.LevBack.lev_of_pin <;> assumption)
