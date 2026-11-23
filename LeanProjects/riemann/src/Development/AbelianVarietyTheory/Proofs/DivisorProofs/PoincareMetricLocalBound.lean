import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormAtContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositivePotentialFormPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticFormTwoSidedBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolydiscBoundaryDistanceEstimateStatement

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff

namespace GlobalTheory

theorem poincarePot_comparable_modelAt : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (K : LocPot X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin m → Option (Fin e)), IsPotential A K → IsPosPot A K → IsBoundary A L s D → IsAdaptedPolydisc A D ψ σ → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ ∀ c : ℝ, 0 < c → TwoSided A K L s D c → ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Metric.ball (0 : Fin e → ℂ) ρ, ψ.symm z ∉ ⋃ i, D i → ∀ w, C⁻¹ * modelAt σ z w ≤ formAt ψ (poincarePot K L s c) z w ∧ formAt ψ (poincarePot K L s c) z w ≤ C * modelAt σ z w := by
  intro e X _ A K m L s D ψ σ hK hKp hB hP
  obtain ⟨ρ, hρ0, hρ, C0, hC0, hT⟩ := GlobalTheory.T.polydisc_boundary_distance_estimate A L s D ψ σ hB hP
  have hψ := hP.1
  have hball := hP.2.1
  have hsub : Metric.closedBall (0 : Fin e → ℂ) (1 / 2) ⊆ ψ.target := fun z hz =>
    hball (Metric.closedBall_subset_ball (by norm_num) hz)
  obtain ⟨δ, CK, hδ, hCK, hKB⟩ := GlobalTheory.T.quadratic_form_two_sided_bound (formAt ψ K) (Metric.closedBall 0 (1 / 2))
    (isCompact_closedBall _ _)
    ((GlobalTheory.T.form_at_continuous A K ψ hK hψ).mono (Set.prod_mono hsub le_rfl))
    (fun z hz w hw => GlobalTheory.T.positive_potential_form_pos A K ψ hK hKp hψ z (hsub hz) w hw)
    (fun z w t => by simp only [formAt, levi_smul_dir]; ring)
  refine ⟨ρ, hρ0, hρ, fun c hc hTS => ?_⟩
  have hpi := Real.pi_pos
  set δ' : ℝ := min (1 / 2) (δ / (4 * c * (m * C0 + 1))) with hδ'
  have hmC : 0 < (m : ℝ) * C0 + 1 := by positivity
  have hδ'0 : 0 < δ' := lt_min (by norm_num) (by positivity)
  have hδ'1 : δ' ≤ 1 / 2 := min_le_left _ _
  have hδ'2 : δ' ≤ δ / (4 * c * (m * C0 + 1)) := min_le_right _ _
  have hcδ : c * (m * (δ' * C0)) ≤ δ / 4 := by
    have h1 : c * δ' * (m * C0 + 1) ≤ δ / 4 := by
      have := mul_le_mul_of_nonneg_left hδ'2 (le_of_lt (mul_pos hc hmC))
      calc c * δ' * (m * C0 + 1) = c * (m * C0 + 1) * δ' := by ring
        _ ≤ c * (m * C0 + 1) * (δ / (4 * c * (m * C0 + 1))) := this
        _ = δ / 4 := by field_simp
    nlinarith [hδ'0.le, hc.le]
  set κ : ℝ := c * δ' / (36 * Real.pi ^ 3) with hκ
  have hκ0 : 0 < κ := by positivity
  set μ : ℝ := min (δ / 4) κ with hμ
  have hμ0 : 0 < μ := lt_min (by positivity) hκ0
  set Cup : ℝ := 2 * CK + c * m + c * m * C0 + 1 with hCup
  have hCup0 : 0 < Cup := by positivity
  refine ⟨max Cup μ⁻¹, lt_max_of_lt_left hCup0, fun z hz hzD w => ?_⟩
  obtain ⟨hext, hTi⟩ := hT z hz hzD w
  have hzc : z ∈ Metric.closedBall (0 : Fin e → ℂ) (1 / 2) :=
    Metric.closedBall_subset_closedBall hρ (Metric.ball_subset_closedBall hz)
  obtain ⟨hKlo, hKhi⟩ := hKB z hzc w
  obtain ⟨hlo, hhi⟩ := hTS ψ hψ z (hsub hzc) hzD w
  set g : Fin e → ℝ := fun k => ‖w k‖ ^ 2 / (‖z k‖ ^ 2 * tOf (z k) ^ 2) with hg
  have hg0 : ∀ k, 0 ≤ g k := fun k => by simp only [hg]; positivity
  set N : ℝ := ∑ k, ‖w k‖ ^ 2 with hN
  have hN0 : 0 ≤ N := by positivity
  set T : Fin m → ℝ := fun i => gradSqAt ψ (rComp L s i) z w / rComp L s i (ψ.symm z) ^ 2 with hTdef
  set E : Fin m → ℝ := fun i => Option.elim (σ i) 0 g with hE
  have hE0 : ∀ i, 0 ≤ E i := fun i => by
    simp only [hE]; cases σ i <;> simp [hg0]
  set Mo := modelAt σ z w with hMo
  have hterm : ∀ k, 0 ≤ (if ∃ i, σ i = some k then g k else ‖w k‖ ^ 2) := fun k => by
    split_ifs
    · exact hg0 k
    · positivity
  have hNM : N ≤ Mo := by
    simp only [hN, hMo, modelAt]
    apply Finset.sum_le_sum
    intro k _
    split_ifs with h
    · obtain ⟨i, hi⟩ := h; exact hext i k hi
    · exact le_rfl
  have hM0 : 0 ≤ Mo := hN0.trans hNM
  have hEM : ∀ i, E i ≤ Mo := by
    intro i
    simp only [hE]
    cases hσ : σ i with
    | none => simpa using hM0
    | some k =>
      simp only [Option.elim]
      have h1 : g k = (if ∃ i, σ i = some k then g k else ‖w k‖ ^ 2) := by
        rw [if_pos ⟨i, hσ⟩]
      rw [h1, hMo, modelAt]
      exact Finset.single_le_sum (f := fun k => if ∃ i, σ i = some k then g k else ‖w k‖ ^ 2)
        (fun k _ => hterm k) (Finset.mem_univ k)
  set Bsum : ℝ := ∑ k, (if ∃ i, σ i = some k then g k else 0) with hBs
  have hMB : Mo ≤ Bsum + N := by
    simp only [hMo, modelAt, hBs, hN, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro k _
    split_ifs
    · linarith [sq_nonneg ‖w k‖]
    · linarith
  have hBE : Bsum ≤ ∑ i, E i := by
    have h1 : Bsum ≤ ∑ k, ∑ i, (if σ i = some k then g k else 0) := by
      simp only [hBs]
      apply Finset.sum_le_sum
      intro k _
      split_ifs with h
      · obtain ⟨i, hi⟩ := h
        have := Finset.single_le_sum (f := fun i => if σ i = some k then g k else 0)
          (fun i _ => by split_ifs <;> simp [hg0]) (Finset.mem_univ i)
        simpa [hi] using this
      · exact Finset.sum_nonneg (fun i _ => by split_ifs <;> simp [hg0])
    rw [Finset.sum_comm] at h1
    refine h1.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    simp only [hE]
    cases σ i with
    | none => simp
    | some k0 => simp [Finset.sum_ite_eq]
  have hKhi' : formAt ψ K z w ≤ CK * N := hKhi
  have hKlo' : δ * N ≤ formAt ψ K z w := hKlo
  have hsumT_hi : ∑ i, T i ≤ ∑ i, E i + m * (C0 * N) := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hTi i).1)
    simpa [Finset.sum_add_distrib, Finset.sum_const, hTdef, hE] using this
  have hsumT_lo : ∑ i, (δ' * E i / (36 * Real.pi ^ 3) - δ' * C0 * N) ≤ ∑ i, T i :=
    Finset.sum_le_sum (fun i _ => (hTi i).2 δ' hδ'0 hδ'1)
  have hsumE : ∑ i, E i ≤ m * Mo := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hEM i)
    simpa using this
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum] at hsumT_lo
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsumT_lo
  have hlo' : formAt ψ K z w / 2 + c * ∑ i, T i ≤ formAt ψ (poincarePot K L s c) z w := hlo
  have hhi' : formAt ψ (poincarePot K L s c) z w ≤ 2 * formAt ψ K z w + c * ∑ i, T i := hhi
  constructor
  · have hμle : μ * Mo ≤ formAt ψ (poincarePot K L s c) z w := by
      have hA : μ * Mo ≤ δ / 4 * N + κ * Bsum := by
        have h1 : μ * Mo ≤ μ * (Bsum + N) := mul_le_mul_of_nonneg_left hMB hμ0.le
        have h2 : μ ≤ δ / 4 := min_le_left _ _
        have h3 : μ ≤ κ := min_le_right _ _
        have hB0 : 0 ≤ Bsum := Finset.sum_nonneg (fun k _ => by split_ifs <;> simp [hg0])
        nlinarith
      have hB2 : κ * Bsum ≤ κ * ∑ i, E i := mul_le_mul_of_nonneg_left hBE hκ0.le
      have hc2 : c * ((δ' * ∑ i, E i) / (36 * Real.pi ^ 3) - m * (δ' * C0 * N)) ≤ c * ∑ i, T i :=
        mul_le_mul_of_nonneg_left hsumT_lo hc.le
      have hκE : κ * ∑ i, E i = c * ((δ' * ∑ i, E i) / (36 * Real.pi ^ 3)) := by
        simp only [hκ]; ring
      rw [mul_sub, ← hκE] at hc2
      have hcδN : c * (m * (δ' * C0 * N)) ≤ δ / 4 * N := by
        have := mul_le_mul_of_nonneg_right hcδ hN0
        have e1 : c * (m * (δ' * C0 * N)) = c * (m * (δ' * C0)) * N := by ring
        rw [e1]; exact this
      linarith
    have hC : μ⁻¹ ≤ max Cup μ⁻¹ := le_max_right _ _
    have : (max Cup μ⁻¹)⁻¹ ≤ μ := by
      rw [inv_le_comm₀ (lt_max_of_lt_left hCup0) hμ0]; exact hC
    calc (max Cup μ⁻¹)⁻¹ * Mo ≤ μ * Mo := mul_le_mul_of_nonneg_right this hM0
      _ ≤ _ := hμle
  · have h1 : formAt ψ (poincarePot K L s c) z w ≤ Cup * Mo := by
      have hc2 : c * ∑ i, T i ≤ c * (∑ i, E i + m * (C0 * N)) :=
        mul_le_mul_of_nonneg_left hsumT_hi hc.le
      have hE2 : c * ∑ i, E i ≤ c * (m * Mo) := mul_le_mul_of_nonneg_left hsumE hc.le
      have hN2 : c * (m * (C0 * N)) ≤ c * (m * (C0 * Mo)) := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hNM hC0.le
      have hK2 : CK * N ≤ CK * Mo := mul_le_mul_of_nonneg_left hNM hCK.le
      rw [mul_add] at hc2
      have e2 : Cup * Mo = 2 * (CK * Mo) + c * (m * Mo) + c * (m * (C0 * Mo)) + Mo := by
        rw [hCup]; ring
      rw [e2]
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hM0)

end GlobalTheory
