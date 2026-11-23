import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.FourGUnit

variable {F : Type} [NontriviallyNormedField F]

theorem integral_ball_char {r : ℕ} [MeasurableSpace F] [BorelSpace F] [IsUltrametricDist F] [ProperSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (hvol : μ (Metric.closedBall 0 1) = 1) (ψ : AddChar F ℂ)
    (hψ : IsStdChar ψ) (v : Fin r → F) :
    ∫ x, {x : Fin r → F | ∀ i, ‖x i‖ ≤ 1}.indicator (fun x => ψ (x ⬝ᵥ v)) x ∂(Measure.pi fun _ => μ) =
      {x : Fin r → F | ∀ i, ‖x i‖ ≤ 1}.indicator 1 v := by
  set S : Set (Fin r → F) := {x | ∀ i, ‖x i‖ ≤ 1} with hSdef
  have hS : S = Set.univ.pi fun _ => Metric.closedBall (0 : F) 1 := by
    ext x; simp [S, Metric.mem_closedBall]
  have hSm : MeasurableSet S := hS ▸ MeasurableSet.univ_pi (fun _ => measurableSet_closedBall)
  by_cases hv : v ∈ S
  · rw [Set.indicator_of_mem hv, integral_indicator hSm,
      setIntegral_congr_fun hSm (g := fun _ => (1 : ℂ)) (fun x hx => ?_), setIntegral_const]
    · rw [Measure.real, hS, Measure.pi_pi]
      simp [hvol]
    · apply hψ.1
      rw [dotProduct]
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
      intro i _
      rw [norm_mul]
      exact mul_le_one₀ (hx i) (norm_nonneg _) (hv i)
  · rw [Set.indicator_of_notMem hv]
    obtain ⟨i, hi⟩ : ∃ i, 1 < ‖v i‖ := by
      simp only [S, Set.mem_setOf_eq, not_forall, not_le] at hv; exact hv
    obtain ⟨x₀, hx₀, hx₀'⟩ := hψ.2
    have hvi : v i ≠ 0 := by
      intro h; rw [h, norm_zero] at hi; linarith
    set z₀ : Fin r → F := Pi.single i (x₀ * (v i)⁻¹) with hz₀def
    have hz₀ : z₀ ∈ S := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [hz₀def, Pi.single_eq_same]
        apply hx₀'
        rw [norm_inv]
        exact inv_lt_one_of_one_lt₀ hi
      · rw [hz₀def, Pi.single_eq_of_ne hj, norm_zero]; exact zero_le_one
    have hχ : ψ (z₀ ⬝ᵥ v) ≠ 1 := by
      rw [hz₀def, single_dotProduct, mul_assoc, inv_mul_cancel₀ hvi, mul_one]
      exact hx₀
    have hadd : ∀ a b : Fin r → F, a ∈ S → b ∈ S → a + b ∈ S := fun a b ha hb i =>
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))
    have key : ∀ z, S.indicator (fun x => ψ (x ⬝ᵥ v)) (z + z₀) =
        S.indicator (fun x => ψ (x ⬝ᵥ v)) z * ψ (z₀ ⬝ᵥ v) := by
      intro z
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem (hadd _ _ hz hz₀), Set.indicator_of_mem hz, add_dotProduct,
          AddChar.map_add_eq_mul]
      · have hneg : -z₀ ∈ S := fun j => by rw [Pi.neg_apply, norm_neg]; exact hz₀ j
        have : z + z₀ ∉ S := fun h => hz (by simpa using hadd _ _ h hneg)
        rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hz, zero_mul]
    have h := integral_add_right_eq_self (μ := Measure.pi fun _ : Fin r => μ)
      (fun z => S.indicator (fun x => ψ (x ⬝ᵥ v)) z) z₀
    simp only [key, integral_mul_const] at h
    have h2 : (∫ z, S.indicator (fun x => ψ (x ⬝ᵥ v)) z ∂(Measure.pi fun _ => μ)) * (ψ (z₀ ⬝ᵥ v) - 1) = 0 := by
      rw [mul_sub, mul_one, h, sub_self]
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact h1
    · exact absurd (sub_eq_zero.mp h1) hχ

end GlobalTheory.JR.FourGUnit

namespace GlobalTheory.JR

open FourGUnit in

theorem fourG_unitG : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    fourG M ψ (unitG r F) = unitG r F := by
  intro F E _ _ _ _ U r M ψ hψ
  letI := M.mF
  haveI := M.bF
  haveI := U.ultraF
  haveI := U.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI := M.haarF
  funext Y
  obtain ⟨A, b, c, l⟩ := Y
  unfold fourG
  set S : Set (Fin r → F) := {x | ∀ i, ‖x i‖ ≤ 1} with hSdef
  set T : Set (Gl r F) := {Y | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧
    ‖Y.2.2.2‖ ≤ 1} with hTdef
  have hT : unitG r F = T.indicator 1 := rfl
  by_cases hP : (∀ i j, ‖A i j‖ ≤ 1) ∧ ‖l‖ ≤ 1
  · have hint : ∀ b' c' : Fin r → F, unitG r F (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') =
        S.indicator (fun x => ψ (x ⬝ᵥ c)) b' * S.indicator (fun x => ψ (x ⬝ᵥ b)) c' := by
      intro b' c'
      by_cases hb' : b' ∈ S
      · by_cases hc' : c' ∈ S
        · rw [hT, Set.indicator_of_mem (show (A, b', c', l) ∈ T from ⟨hP.1, hb', hc', hP.2⟩),
            Set.indicator_of_mem hb', Set.indicator_of_mem hc', Pi.one_apply, one_mul,
            AddChar.map_add_eq_mul, dotProduct_comm c b', mul_comm]
        · rw [hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hc' h.2.2.1),
            Set.indicator_of_notMem hc', zero_mul, mul_zero]
      · rw [hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hb' h.2.1),
          Set.indicator_of_notMem hb', zero_mul, zero_mul]
    have hball : ∀ v : Fin r → F, ∫ x, S.indicator (fun x => ψ (x ⬝ᵥ v)) x ∂(Measure.pi fun _ => M.μF) =
        S.indicator 1 v := integral_ball_char M.μF M.volF ψ hψ
    simp_rw [hint, integral_const_mul, hball, integral_mul_const, hball]
    by_cases hb : b ∈ S
    · by_cases hc : c ∈ S
      · rw [hT, Set.indicator_of_mem (show (A, b, c, l) ∈ T from ⟨hP.1, hb, hc, hP.2⟩),
          Set.indicator_of_mem hb, Set.indicator_of_mem hc]
        simp
      · rw [hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hc h.2.2.1),
          Set.indicator_of_notMem hc, zero_mul]
    · rw [hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hb h.2.1),
        Set.indicator_of_notMem hb, mul_zero]
  · have h0 : ∀ b' c' : Fin r → F, unitG r F (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') = 0 := by
      intro b' c'
      rw [hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hP ⟨h.1, h.2.2.2⟩),
        zero_mul]
    simp_rw [h0, integral_zero]
    rw [hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hP ⟨h.1, h.2.2.2⟩)]

end GlobalTheory.JR
