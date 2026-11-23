import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.YcUnitary

noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting

variable {N r : ℕ} (ε : Fin N → Bool) (F G : Fin (r + 1) → Fin N → ℂ) (T T' : ℝ) (π : Fin (r + 1) → Fin (r + 1))
  (blk : Fin (r + 1) → ℕ)
  (hFF : ∀ a b, hJ ε (F a) (F b) = lastDiag (-(T : ℂ)) a b)
  (hGG : ∀ a b, hJ ε (G a) (G b) = lastDiag (-(T' : ℂ)) a b)
  (hπ : ∀ a, π (π a) = a) (hblk : ∀ a, blk (π a) = blk a) (hanti : ∀ a b, blk a = blk b → a < b → π b < π a)
  (hZ : ∀ c b, Zm ε F G c b ≠ 0 ↔ c = π b)
  (hgap : 1 - (T : ℂ) * T' * ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r) *
    starRingEnd ℂ ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r))) ≠ 0)

include hFF hGG hπ hZ hgap in
theorem Yc_G {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (b : Fin (r + 1)) :
    Yc ε F G C *ᵥ G b = ∑ b', C b' b • G b' := by
  have hΓ := gram_unit (ε := ε) (F := F) (G := G) (T := T) (T' := T') (π := π) (hFF := hFF)
    (hGG := hGG) (hπ := hπ) (hZ := hZ) (hgap := hgap)
  have hW : Yc ε F G C * Wfg F G = Wfg F G * (1 + Mm ε F G C) := rankUpdate_mul _ _ _ hΓ
  have hGcol : G b = Wfg F G *ᵥ Pi.single (Sum.inr b) 1 := by
    funext p
    rw [Matrix.mulVec_single]
    simp [Wfg]
  rw [hGcol, Matrix.mulVec_mulVec, hW, ← Matrix.mulVec_mulVec, Matrix.mulVec_single]
  funext p
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Wfg, Mm, Matrix.one_apply, Finset.sum_apply, mul_comm]

include hFF hGG hπ hZ hgap in
theorem Yc_F {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (a : Fin (r + 1)) :
    Yc ε F G C *ᵥ F a = ∑ a', Am ε F G C a' a • F a' := by
  have hΓ := gram_unit (ε := ε) (F := F) (G := G) (T := T) (T' := T') (π := π) (hFF := hFF)
    (hGG := hGG) (hπ := hπ) (hZ := hZ) (hgap := hgap)
  have hW : Yc ε F G C * Wfg F G = Wfg F G * (1 + Mm ε F G C) := rankUpdate_mul _ _ _ hΓ
  have hFcol : F a = Wfg F G *ᵥ Pi.single (Sum.inl a) 1 := by
    funext p
    rw [Matrix.mulVec_single]
    simp [Wfg]
  rw [hFcol, Matrix.mulVec_mulVec, hW, ← Matrix.mulVec_mulVec, Matrix.mulVec_single]
  funext p
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Wfg, Mm, Matrix.one_apply, Finset.sum_apply, mul_comm]

theorem rowLast {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) (k : Fin (r + 1)) :
    C (Fin.last r) k = if k = Fin.last r then 1 else 0 := by
  obtain ⟨hdiag, hup⟩ := hC
  split_ifs with hk
  · rw [hk]
    exact hdiag _
  · by_contra h
    have h1 := (hup _ _ h).1
    exact hk (le_antisymm (Fin.le_last k) h1)

include hπ hblk hanti in
theorem colMin {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) (b : Fin (r + 1)) :
    C b (π (Fin.last r)) = if b = π (Fin.last r) then 1 else 0 := by
  obtain ⟨hdiag, hup⟩ := hC
  split_ifs with hb
  · rw [hb]
    exact hdiag _
  · by_contra h
    obtain ⟨hle, hbl⟩ := hup _ _ h
    have hlt : b < π (Fin.last r) := lt_of_le_of_ne hle hb
    have h2 := hanti b (π (Fin.last r)) hbl hlt
    rw [hπ] at h2
    exact absurd (Fin.le_last (π b)) (not_le.mpr h2)

end Formalism.L2.S.L6.UnitaryStandardVectors
