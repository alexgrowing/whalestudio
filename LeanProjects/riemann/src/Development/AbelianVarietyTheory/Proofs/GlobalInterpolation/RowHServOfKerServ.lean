import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.R1

theorem row_hServ_of_kerServ : ∀ (Q : V4.Slot) (Lk : LkT Bundle),
    Row Q Lk (GlobalTheory.Svd.ServH fun _ _ _ (b : Bundle _ _ _) => b.R.T.ker) → R1.SerreConditionAtBundlePoints Q Lk := by
  intro Q Lk h
  refine Row.imp h fun 𝒜 σ _ hs => ?_
  obtain ⟨⟨a, ha, hK⟩, hA⟩ := hs
  refine ⟨⟨a, ha, fun e he hle => ?_⟩, ⟨a, ha, fun e he hle => ?_⟩⟩
  · obtain ⟨K, hK⟩ := hK e he hle
    exact ⟨K, fun Fm CH hc hL => hK Fm CH (GlobalTheory.Cp.d3_a hc) hL⟩
  · obtain ⟨K, _⟩ := hK e he hle
    exact ⟨K, fun Fm _ _ _ hc x hx _ i => hA Fm (GlobalTheory.Cp.d3_a hc) x hx i⟩

end GlobalTheory.Fc.R1
