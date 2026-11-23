import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemDomOfIsom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CountAsmPfB
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

namespace GlobalTheory.CuspEmb

theorem twoLevels_mul_mem_SS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la mu : Wt M.Ψ r) (F G : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → G ∈ M.SS mu → F * G ∈ M.SS (la + mu) := by
  intro E _ _ _ r U C _ _ M la mu F G hF hG c
  have hP := hF c
  have hQ := (hG c).1
  have h := ReciprocityTheory.ChartRestriction.G.AR.Up.ss_mul_pow (M.comp c).toData hP hQ 1
  have hw : castWt (M.comp_Ψ c) (la + mu) =
      castWt (M.comp_Ψ c) la + 1 • castWt (M.comp_Ψ c) mu := by
    rw [one_smul]; funext τ; rfl
  rw [hw]
  rw [pow_one] at h
  exact h

end GlobalTheory.CuspEmb
