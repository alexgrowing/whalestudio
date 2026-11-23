import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.T2SpaceLatticeVOfGoodSituation
import Formalism.SharpRestriction.LevelLetterCocycles.ZlWCbInjective
import Formalism.SharpRestriction.LevelLetterCocycles.NormLtOneIffToZMod

noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo Formalism.MainNotions.LocalSituation Topology Filter

variable {l : ℕ} [hl : Fact l.Prime]

theorem zetaQ_pow (P : LocPrime l) (j k : ℕ) : P.ζQ (j + k) ^ (l ^ k) = P.ζQ j := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, P.ζQ_succ, ih]

theorem chiQ_norm (P : LocPrime l) (h : GQ l) : ‖(P.χQ h : ℚ_[l])‖ = 1 := by
  have hroot : P.ζQ 1 ^ l = 1 := by
    have h0 := zetaQ_pow P 0 1
    rwa [zero_add, P.ζQ_zero, pow_one] at h0
  have hle : ∀ g : GQ l, ‖(P.χQ g : ℚ_[l])‖ ≤ 1 := by
    intro g
    obtain ⟨a, ha, -⟩ := P.χQ_cyc g 1 (P.ζQ 1) (by rwa [pow_one])
    have hA : ‖(a : ℚ_[l])‖ ≤ 1 := by
      have h2 : ‖((a : ℤ) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-((0 : ℕ) : ℤ)) := by
        first
          | exact (Padic.norm_int_le_pow_iff_dvd (a : ℤ) 0).2 (by simp)
          | exact (padicNormE.norm_int_le_pow_iff_dvd (a : ℤ) 0).2 (by simp)
      simpa using h2
    have hl1 : (l : ℝ) ^ (-((1 : ℕ) : ℤ)) ≤ 1 := by
      have h3 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.one_lt.le
      simp only [Nat.cast_one, zpow_neg, zpow_one]
      first
        | exact inv_le_one_of_one_le₀ h3
        | exact inv_le_one h3
    calc ‖(P.χQ g : ℚ_[l])‖ = ‖((P.χQ g : ℚ_[l]) - a) + a‖ := by rw [sub_add_cancel]
      _ ≤ max ‖(P.χQ g : ℚ_[l]) - a‖ ‖(a : ℚ_[l])‖ := by
        first
          | exact Padic.nonarchimedean _ _
          | exact padicNormE.nonarchimedean _ _
          | exact IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le (ha.trans hl1) hA
  have h1 := hle h
  have h2 := hle h⁻¹
  have hmul : ‖(P.χQ h : ℚ_[l])‖ * ‖(P.χQ h⁻¹ : ℚ_[l])‖ = 1 := by
    rw [← norm_mul, ← Units.val_mul, ← map_mul]
    simp
  exact le_antisymm h1 (by nlinarith [norm_nonneg (P.χQ h : ℚ_[l]), norm_nonneg (P.χQ h⁻¹ : ℚ_[l])])

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators
