import Mathlib

open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem relIndex_ratio_cocycle : ∀ (G : Type) [Group G] (A B C : Subgroup G), A.relIndex B ≠ 0 → B.relIndex A ≠ 0 → B.relIndex C ≠ 0 → C.relIndex B ≠ 0 → A.relIndex C ≠ 0 ∧ C.relIndex A ≠ 0 ∧ B.relIndex A * C.relIndex B * A.relIndex C = A.relIndex B * B.relIndex C * C.relIndex A := by
  intro G _ A B C hAB hBA hBC hCB
  have hAC : A.relIndex C ≠ 0 := Subgroup.relIndex_ne_zero_trans hAB hBC
  have hCA : C.relIndex A ≠ 0 := Subgroup.relIndex_ne_zero_trans hCB hBA
  refine ⟨hAC, hCA, ?_⟩
  set T : Subgroup G := A ⊓ B ⊓ C with hT
  have hTAB : T ≤ A ⊓ B := inf_le_left
  have hTBC : T ≤ B ⊓ C := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hTAC : T ≤ A ⊓ C := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have h1 := Subgroup.relIndex_mul_relIndex T (A ⊓ B) A hTAB inf_le_left
  have h2 := Subgroup.relIndex_mul_relIndex T (A ⊓ B) B hTAB inf_le_right
  have h3 := Subgroup.relIndex_mul_relIndex T (B ⊓ C) B hTBC inf_le_left
  have h4 := Subgroup.relIndex_mul_relIndex T (B ⊓ C) C hTBC inf_le_right
  have h5 := Subgroup.relIndex_mul_relIndex T (A ⊓ C) A hTAC inf_le_left
  have h6 := Subgroup.relIndex_mul_relIndex T (A ⊓ C) C hTAC inf_le_right
  rw [Subgroup.inf_relIndex_left A B] at h1
  rw [Subgroup.inf_relIndex_left] at h3 h5
  rw [Subgroup.inf_relIndex_right] at h2 h4 h6
  have hTC : T.relIndex C ≠ 0 := by
    rw [hT, Subgroup.inf_relIndex_right]
    exact Subgroup.relIndex_inf_ne_zero hAC hBC
  have hTB : T.relIndex B ≠ 0 := Subgroup.relIndex_ne_zero_trans hTC hCB
  have hx : T.relIndex (A ⊓ B) ≠ 0 := left_ne_zero_of_mul (h2 ▸ hTB)
  have hy : T.relIndex (B ⊓ C) ≠ 0 := left_ne_zero_of_mul (h4 ▸ hTC)
  have hz : T.relIndex (A ⊓ C) ≠ 0 := left_ne_zero_of_mul (h6 ▸ hTC)
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hx hy) hz)
  calc T.relIndex (A ⊓ B) * T.relIndex (B ⊓ C) * T.relIndex (A ⊓ C) *
        (B.relIndex A * C.relIndex B * A.relIndex C)
      = (T.relIndex (A ⊓ B) * B.relIndex A) * (T.relIndex (B ⊓ C) * C.relIndex B) *
        (T.relIndex (A ⊓ C) * A.relIndex C) := by ring
    _ = (T.relIndex (A ⊓ C) * C.relIndex A) * (T.relIndex (A ⊓ B) * A.relIndex B) *
        (T.relIndex (B ⊓ C) * B.relIndex C) := by rw [h1, h2, h3, h4, h5, h6]
    _ = _ := by ring

end GlobalTheory.CompanionTheory.Ar.Cmp
