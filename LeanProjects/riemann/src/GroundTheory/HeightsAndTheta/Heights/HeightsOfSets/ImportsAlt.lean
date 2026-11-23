import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Comparison
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

theorem HeightComparison.proof (hV : CurveDivVertical.Statement) : HeightComparison.Statement := by
  intro K _ ι _ I A H hI hA hH hHa
  set m : ℕ := ∑ k, (A.a k).natAbs
  have hm : ∀ k, (A.a k).natAbs ≤ m := fun k ↦
    Finset.single_le_sum (f := fun k ↦ (A.a k).natAbs) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ k)
  have hHk : ∀ k, H.a k = 1 := fun k ↦ by rw [hHa]; rfl
  set Ep := (powLine H m).tensor (invLine A)
  set Em := (powLine H m).tensor A
  have hPow := isSmoothHerm_powLine hH m
  have hEp : IsSmoothHerm Ep := isSmoothHerm_tensor hPow (isSmoothHerm_invLine hA)
  have hEm : IsSmoothHerm Em := isSmoothHerm_tensor hPow hA
  set dp : K → ℕ := fun k ↦ ((m : ℤ) - A.a k).toNat
  set dm : K → ℕ := fun k ↦ ((m : ℤ) + A.a k).toNat
  have hdp : ∀ k, Ep.a k = dp k := fun k ↦ by
    have := hm k
    show (powLine H m).a k + -A.a k = (((m : ℤ) - A.a k).toNat : ℤ)
    rw [powLine_a, hHk]
    omega
  have hdm : ∀ k, Em.a k = dm k := fun k ↦ by
    have := hm k
    show (powLine H m).a k + A.a k = (((m : ℤ) + A.a k).toNat : ℤ)
    rw [powLine_a, hHk]
    omega
  obtain ⟨Mp, hMp1, hMp⟩ := exists_chartMon_bound hEp hdp
  obtain ⟨Mm, hMm1, hMm⟩ := exists_chartMon_bound hEm hdm
  have hMp0 : 0 < Mp := by linarith
  have hMm0 : 0 < Mm := by linarith
  set C := max (Real.log Mp) (Real.log Mm)
  refine ⟨m, C, fun W hW ↦ ?_⟩
  have hC : 0 ≤ C := le_max_of_le_left (Real.log_nonneg hMp1)
  unfold height
  rcases Nat.eq_zero_or_pos (degC W) with hdeg | hdeg
  · simp [hdeg, hC]
  obtain ⟨c, hc⟩ := exists_chartMon_notMem hW
  have hp := inter_nonneg I hV hI hW (isSmoothHerm_tensor hEp (isSmoothHerm_constLine Mp hMp0))
    (d := dp) (fun k ↦ by show Ep.a k + 0 = _; rw [add_zero, hdp k]) c (hc dp)
    (fun z hz ↦ by show _ ≤ Ep.h z * Mp; rw [mul_comm]; exact hMp c z hz.1)
  have hn := inter_nonneg I hV hI hW (isSmoothHerm_tensor hEm (isSmoothHerm_constLine Mm hMm0))
    (d := dm) (fun k ↦ by show Em.a k + 0 = _; rw [add_zero, hdm k]) c (hc dm)
    (fun z hz ↦ by show _ ≤ Em.h z * Mm; rw [mul_comm]; exact hMm c z hz.1)
  rw [inter_tensor I hI hW hEp (isSmoothHerm_constLine Mp hMp0),
    inter_tensor I hI hW hPow (isSmoothHerm_invLine hA), inter_powLine I hI hW hH,
    inter_invLine I hI hW hA] at hp
  rw [inter_tensor I hI hW hEm (isSmoothHerm_constLine Mm hMm0), inter_tensor I hI hW hPow hA,
    inter_powLine I hI hW hH] at hn
  have hcp := inter_constLine_le I hI hW hMp0 hMp1 hdeg
  have hcn := inter_constLine_le I hI hW hMm0 hMm1 hdeg
  have hD : (0 : ℝ) < degC W := by exact_mod_cast hdeg
  have hCp : Real.log Mp * degC W ≤ C * degC W :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hD.le
  have hCn : Real.log Mm * degC W ≤ C * degC W :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hD.le
  rw [abs_div, abs_of_pos hD, div_le_iff₀ hD, add_mul, mul_assoc, div_mul_cancel₀ _ hD.ne', abs_le]
  constructor <;> linarith

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
