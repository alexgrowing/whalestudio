import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeEqLintegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntNearOfClosureShort
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeSumSqBallPosLtTop
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

theorem log_ellCount_near : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ), A.PosDef → ∀ (T : Set (ι → ℤ)) (ρ R : ℝ), 0 ≤ ρ → 0 < R → AddSubgroup.closure T = ⊤ → (∀ z ∈ T, ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ ρ ^ 2) → 2 * Fintype.card ι * ρ ≤ R → {z : ι → ℤ | ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R ^ 2}.Finite ∧ |Real.log (ellCount A R) - (Fintype.card ι * Real.log R - Real.log A.det / 2 + Real.log (volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)| ≤ Fintype.card ι * Real.log 2 := by
  intro ι _ _ A hA T ρ R hρ hR hT hTz hRρ
  set n : ℕ := Fintype.card ι with hn
  set s : ℝ := n * ρ with hs
  have hs0 : 0 ≤ s := by positivity
  have hsR : s ≤ R / 2 := by rw [hs]; linarith
  have hnear := exists_int_near_of_closure_short ι A hA T ρ hρ hT hTz
  have hup := ellCount_volume ι A hA s R hs0 hR.le hnear
  have hlo := (ellCount_volume ι A hA s (R - s) hs0 (by linarith) hnear).2.1
  rw [sub_add_cancel] at hlo
  refine ⟨hup.1, ?_⟩
  obtain ⟨-, hω0, hωt⟩ := volume_ellipsoid ι A hA 0 le_rfl
  set ω : ENNReal := volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1} with hω
  have hVr : ∀ r : ℝ, 0 ≤ r → (volume {x : ι → ℝ | ∑ i, ∑ j, A i j * x i * x j ≤ r ^ 2}).toReal
      = r ^ n / Real.sqrt A.det * ω.toReal := by
    intro r hr
    rw [(volume_ellipsoid ι A hA r hr).1, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hVfin : ∀ r : ℝ, 0 ≤ r → volume {x : ι → ℝ | ∑ i, ∑ j, A i j * x i * x j ≤ r ^ 2} ≠ ⊤ := by
    intro r hr
    rw [(volume_ellipsoid ι A hA r hr).1]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωt.ne
  have hmono : ∀ r r' : ℝ, 0 ≤ r → r ≤ r' → volume {x : ι → ℝ | ∑ i, ∑ j, A i j * x i * x j ≤ r ^ 2}
      ≤ volume {x : ι → ℝ | ∑ i, ∑ j, A i j * x i * x j ≤ r' ^ 2} := by
    intro r r' hr hrr
    apply measure_mono
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    nlinarith
  have hlo' := (hmono (R / 2) (R - s) (by positivity) (by linarith)).trans hlo
  have hup' := hup.2.2.trans (hmono (R + s) (2 * R) (by linarith) (by linarith))
  have hloR : (R / 2) ^ n / Real.sqrt A.det * ω.toReal ≤ (ellCount A R : ℝ) := by
    rw [← hVr _ (by positivity)]
    have := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hlo'
    simpa using this
  have hupR : (ellCount A R : ℝ) ≤ (2 * R) ^ n / Real.sqrt A.det * ω.toReal := by
    rw [← hVr _ (by positivity)]
    have := ENNReal.toReal_mono (hVfin _ (by positivity)) hup'
    simpa using this
  have hdet := hA.det_pos
  have hωr : 0 < ω.toReal := ENNReal.toReal_pos hω0.ne' hωt.ne
  set K : ℝ := ω.toReal / Real.sqrt A.det with hK
  have hK0 : 0 < K := by positivity
  have hlogK : Real.log K = Real.log ω.toReal - Real.log A.det / 2 := by
    rw [hK, Real.log_div hωr.ne' (Real.sqrt_pos.2 hdet).ne', Real.log_sqrt hdet.le]
  have e1 : (R / 2) ^ n / Real.sqrt A.det * ω.toReal = (R / 2) ^ n * K := by rw [hK]; ring
  have e2 : (2 * R) ^ n / Real.sqrt A.det * ω.toReal = (2 * R) ^ n * K := by rw [hK]; ring
  rw [e1] at hloR
  rw [e2] at hupR
  have hp1 : 0 < (R / 2) ^ n * K := by positivity
  have hc : 0 < (ellCount A R : ℝ) := hp1.trans_le hloR
  have l1 := Real.log_le_log hp1 hloR
  have l2 := Real.log_le_log hc hupR
  rw [Real.log_mul (by positivity) hK0.ne', Real.log_pow, Real.log_div hR.ne' two_ne_zero] at l1
  rw [Real.log_mul (by positivity) hK0.ne', Real.log_pow, Real.log_mul two_ne_zero hR.ne'] at l2
  rw [mul_sub] at l1
  rw [mul_add] at l2
  rw [abs_le]
  constructor <;> linarith

end GlobalTheory.HSAmp
