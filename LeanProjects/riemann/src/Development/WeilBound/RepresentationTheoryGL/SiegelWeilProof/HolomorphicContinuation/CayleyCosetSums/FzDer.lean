import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ReConjMulLe

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.FL
open PositivityTheory.Rg.Sw.LVs.II (cE)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem fzDer : FzDer := by
  intro n m e w Z b
  have hX : IsLie (if b = true then dir1 Z else dir2 Z) := lie_dir Z b
  haveI := kRCpt n
  have hc1 : Continuous fun k : KR n => rD (if b = true then dir1 Z else dir2 Z) (mR (k : GR n)) :=
    (continuous_rD _).comp continuous_subtype_val
  have hc2 : Continuous fun k : KR n => rA (if b = true then dir1 Z else dir2 Z) (mR (k : GR n)) :=
    (continuous_rA _).comp continuous_subtype_val
  obtain ⟨C1, hC1⟩ := (isCompact_range hc1).isBounded.exists_norm_le
  obtain ⟨C2, hC2⟩ := (isCompact_range hc2).isBounded.exists_norm_le
  refine ⟨|(e : ℝ)| * max C1 0 + ((m : ℝ) + 2 * ‖w‖) * max C2 0, by positivity, fun y => ?_⟩
  obtain ⟨p, k, hp, hk, rfl⟩ := iwa n y
  obtain ⟨R, hR, hRb⟩ := fz_deriv (x := mR (p * k)) hX (p * k).2 m e w
  refine ⟨R, ?_, ?_⟩
  · simp only [cE_eq_exp]
    exact hR
  · refine hRb.trans ?_
    have e1 : rD (if b = true then dir1 Z else dir2 Z) (mR (p * k)) =
        rD (if b = true then dir1 Z else dir2 Z) (mR k) := by
      rw [mR_mul, rD_up]
    have e2 : rA (if b = true then dir1 Z else dir2 Z) (mR (p * k)) =
        rA (if b = true then dir1 Z else dir2 Z) (mR k) := by
      rw [mR_mul, rA_up _ _ _ hp]
    have b1 : ‖rD (if b = true then dir1 Z else dir2 Z) (mR k)‖ ≤ max C1 0 :=
      (hC1 _ ⟨⟨k, hk⟩, rfl⟩).trans (le_max_left _ _)
    have b2 : ‖rA (if b = true then dir1 Z else dir2 Z) (mR k)‖ ≤ max C2 0 :=
      (hC2 _ ⟨⟨k, hk⟩, rfl⟩).trans (le_max_left _ _)
    rw [e1, e2, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    gcongr

end PositivityTheory.Rg.Sw.HSt
