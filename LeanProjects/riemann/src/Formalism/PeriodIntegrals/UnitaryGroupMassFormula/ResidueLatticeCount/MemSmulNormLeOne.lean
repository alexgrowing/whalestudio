import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.UnitPreserving

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped ENNReal Classical Pointwise

noncomputable section

namespace PI.Residue

variable (K : Type) [Field K] [NumberField K]

def cHalf : ℝ := (1 / 2 : ℝ) ^ ((1 : ℝ) / Module.finrank ℚ K)

theorem cHalf_pos : 0 < cHalf K := Real.rpow_pos_of_pos (by norm_num) _

theorem cHalf_pow : cHalf K ^ Module.finrank ℚ K = 1 / 2 := by
  have hm : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  rw [cHalf, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), one_div_mul_cancel hm,
    Real.rpow_one]

theorem mem_smul_normLeOne (y : mixedSpace K) :
    y ∈ cHalf K • normLeOne K ↔ y ∈ fundamentalCone K ∧ mixedEmbedding.norm y ≤ 1 / 2 := by
  have hc := cHalf_pos K
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne', mem_normLeOne,
    smul_mem_iff_mem (inv_ne_zero hc.ne'), mixedEmbedding.norm_smul, abs_of_pos (inv_pos.2 hc),
    inv_pow, cHalf_pow]
  refine and_congr_right fun _ => ?_
  constructor <;> intro h <;> linarith

theorem shell_eq : shell K = normLeOne K \ (cHalf K • normLeOne K) := by
  ext y
  rw [Set.mem_sdiff, mem_smul_normLeOne, mem_normLeOne]
  simp only [shell, Set.mem_ofPred_eq, not_and, not_le]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3⟩, fun _ => h2⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨h1, h2 h1, h3⟩

theorem smul_subset : cHalf K • normLeOne K ⊆ normLeOne K := by
  intro y hy
  rw [mem_smul_normLeOne] at hy
  exact mem_normLeOne.2 ⟨hy.1, hy.2.trans (by norm_num)⟩

theorem shellVolume : ShellVolume := by
  intro K _ _
  have hc := cHalf_pos K
  have hV : volume (normLeOne K) = vfac K * ENNReal.ofReal (regulator K) := by
    rw [volume_normLeOne, vfac]
  have hfin : volume (normLeOne K) ≠ ⊤ := (isBounded_normLeOne K).measure_lt_top.ne
  have hs : volume (cHalf K • normLeOne K) = volume (normLeOne K) / 2 := by
    rw [Measure.addHaar_smul, mixedEmbedding.finrank, cHalf_pow, abs_of_pos (by norm_num),
      ENNReal.div_eq_inv_mul]
    congr 1
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hm : MeasurableSet (cHalf K • normLeOne K) :=
    (measurableSet_normLeOne K).const_smul₀ _
  rw [shell_eq, measure_sdiff (smul_subset K) hm.nullMeasurableSet
    (ne_top_of_le_ne_top hfin (measure_mono (smul_subset K))), hs, ← hV]
  exact ENNReal.sub_half hfin

end PI.Residue
