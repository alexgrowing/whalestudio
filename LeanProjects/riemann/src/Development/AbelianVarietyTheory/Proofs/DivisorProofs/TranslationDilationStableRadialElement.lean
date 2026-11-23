import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD

noncomputable section

open ValuativeRel

namespace GlobalTheory.PrinTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def dilF (Φ : k → ℂ) (z : k) : k → ℂ := fun x => Φ (z * x)

theorem dilF_eq_of_close {Φ : k → ℂ} (r R : kˣ)
    (hLC : ∀ x y : k, valuation k y ≤ valuation k (r : k) → Φ (x + y) = Φ x)
    (hCS : ∀ x : k, valuation k (R : k) < valuation k x → Φ x = 0) {z w : k}
    (hz : valuation k z = 1) (hw : valuation k w = 1)
    (hzw : valuation k (w - z) ≤ valuation k (r : k) * (valuation k (R : k))⁻¹) :
    dilF Φ w = dilF Φ z := by
  have hR0 : valuation k (R : k) ≠ 0 := by simp
  funext x
  simp only [dilF]
  by_cases hx : valuation k x ≤ valuation k (R : k)
  · have e : w * x = z * x + (w - z) * x := by ring
    rw [e, hLC]
    rw [map_mul]
    calc valuation k (w - z) * valuation k x
        ≤ (valuation k (r : k) * (valuation k (R : k))⁻¹) * valuation k (R : k) := mul_le_mul' hzw hx
      _ = valuation k (r : k) := by rw [mul_assoc, inv_mul_cancel₀ hR0, mul_one]
  · push_neg at hx
    rw [hCS, hCS]
    · simpa [map_mul, hz] using hx
    · simpa [map_mul, hw] using hx

theorem finite_dilF {Φ : k → ℂ} (r R : kˣ)
    (hLC : ∀ x y : k, valuation k y ≤ valuation k (r : k) → Φ (x + y) = Φ x)
    (hCS : ∀ x : k, valuation k (R : k) < valuation k x → Φ x = 0) :
    (dilF Φ '' {z : k | valuation k z = 1}).Finite := by
  set c : ValueGroupWithZero k := min (valuation k (r : k) * (valuation k (R : k))⁻¹) 1 with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    rcases min_choice (valuation k (r : k) * (valuation k (R : k))⁻¹) 1 with h | h <;> rw [h] <;> simp
  let U : k → Set k := fun z => {w : k | valuation k (w - z) < c}
  have hU : ∀ z ∈ {z : k | valuation k z ≤ 1}, U z ∈ nhds z := fun z _ =>
    (IsValuativeTopology.mem_nhds_iff').2 ⟨Units.mk0 c hc0, by
      intro w hw
      show valuation k (w - z) < c
      simpa using hw⟩
  obtain ⟨t, -, ht⟩ := (IsNonarchimedeanLocalField.isCompact_closedBall k 1).elim_nhds_subcover U hU
  refine ((t.finite_toSet).image (dilF Φ)).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  have hw' : valuation k w = 1 := hw
  have hmem : w ∈ ⋃ z ∈ t, U z := ht (le_of_eq hw')
  simp only [Set.mem_iUnion, exists_prop] at hmem
  obtain ⟨z, hzt, hwz⟩ := hmem
  have hwz' : valuation k (w - z) < c := hwz
  have hz1 : valuation k z = 1 := by
    have h1 : valuation k (z - w) < valuation k w := by
      rw [hw', ← Valuation.map_neg, neg_sub]
      exact lt_of_lt_of_le hwz' (min_le_right _ _)
    exact (Valuation.map_eq_of_sub_lt (valuation k) h1).trans hw'
  refine ⟨z, hzt, ?_⟩
  exact (dilF_eq_of_close r R hLC hCS hz1 hw' (le_trans hwz'.le (min_le_left _ _))).symm

theorem exists_radial_mem_of_stable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (W : Submodule ℂ (k → ℂ)), (∀ Φ ∈ W, ∀ y : k, (fun x => Φ (x + y)) ∈ W) →
    (∀ Φ ∈ W, ∀ a : kˣ, (fun x => Φ (a * x)) ∈ W) → ∀ Φ ∈ W, Φ ≠ 0 → GlobalTheory.PrinTwo.IsLC Φ → GlobalTheory.PrinTwo.IsCS Φ →
    ∃ R ∈ W, GlobalTheory.PrinTwo.IsLC R ∧ GlobalTheory.PrinTwo.IsCS R ∧ R 0 ≠ 0 ∧
      ∀ (u : kˣ) (x : k), ValuativeRel.valuation k (u : k) = 1 → R (u * x) = R x := by
  intro k _ _ _ _ W htr hdil Φ hΦW hΦ0 hLC hCS
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, Φ x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hΦ0 (funext h)
  obtain ⟨r, hr⟩ := hLC
  obtain ⟨R₀, hR₀⟩ := hCS
  set Ψ : k → ℂ := fun x => Φ (x + x₀) with hΨ
  have hΨW : Ψ ∈ W := htr Φ hΦW x₀
  have hΨ0 : Ψ 0 ≠ 0 := by simpa [Ψ] using hx₀
  have hΨLC : ∀ x y : k, valuation k y ≤ valuation k (r : k) → Ψ (x + y) = Ψ x := by
    intro x y hy
    simp only [Ψ]
    rw [add_right_comm]
    exact hr _ _ hy
  have hx₀R : valuation k x₀ ≤ valuation k (R₀ : k) := by
    by_contra h
    push_neg at h
    exact hx₀ (hR₀ _ h)
  have hΨCS : ∀ x : k, valuation k (R₀ : k) < valuation k x → Ψ x = 0 := by
    intro x hx
    apply hR₀
    rw [Valuation.map_add_eq_of_lt_left (valuation k) (lt_of_le_of_lt hx₀R hx)]
    exact hx
  have hS := finite_dilF r R₀ hΨLC hΨCS
  set T := hS.toFinset with hT
  have hmemT : ∀ ψ ∈ T, ∃ z : k, valuation k z = 1 ∧ dilF Ψ z = ψ := by
    intro ψ hψ
    rw [hT, Set.Finite.mem_toFinset] at hψ
    exact hψ
  have happ : ∀ x : k, (∑ ψ ∈ T, ψ) x = ∑ ψ ∈ T, ψ x := fun x => Finset.sum_apply x T fun ψ => ψ
  refine ⟨∑ ψ ∈ T, ψ, ?_, ?_, ?_, ?_, ?_⟩
  · refine Submodule.sum_mem W fun ψ hψ => ?_
    obtain ⟨z, hz, rfl⟩ := hmemT ψ hψ
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, map_zero] at hz
      exact zero_ne_one hz
    show (fun x => Ψ (z * x)) ∈ W
    simpa using hdil Ψ hΨW (Units.mk0 z hz0)
  · refine ⟨r, fun x y hy => ?_⟩
    rw [happ, happ]
    refine Finset.sum_congr rfl fun ψ hψ => ?_
    obtain ⟨z, hz, rfl⟩ := hmemT ψ hψ
    simp only [dilF]
    rw [mul_add, hΨLC]
    simpa [map_mul, hz] using hy
  · refine ⟨R₀, fun x hx => ?_⟩
    rw [happ]
    refine Finset.sum_eq_zero fun ψ hψ => ?_
    obtain ⟨z, hz, rfl⟩ := hmemT ψ hψ
    simp only [dilF]
    apply hΨCS
    simpa [map_mul, hz] using hx
  · rw [happ]
    have h1 : ∀ ψ ∈ T, ψ 0 = Ψ 0 := by
      intro ψ hψ
      obtain ⟨z, hz, rfl⟩ := hmemT ψ hψ
      simp [dilF]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
    refine mul_ne_zero ?_ hΨ0
    have hne : T.Nonempty := ⟨dilF Ψ 1, by rw [hT, Set.Finite.mem_toFinset]; exact ⟨1, by simp, rfl⟩⟩
    exact_mod_cast hne.card_pos.ne'
  · intro u x hu
    rw [happ, happ]
    refine Finset.sum_nbij' (fun ψ => fun y => ψ ((u : k) * y)) (fun ψ => fun y => ψ (((u⁻¹ : kˣ) : k) * y))
      ?_ ?_ ?_ ?_ ?_
    · intro ψ hψ
      obtain ⟨z, hz, rfl⟩ := hmemT ψ hψ
      rw [hT, Set.Finite.mem_toFinset]
      refine ⟨z * u, by simp [map_mul, hz, hu], ?_⟩
      funext y
      simp [dilF, mul_assoc]
    · intro ψ hψ
      obtain ⟨z, hz, rfl⟩ := hmemT ψ hψ
      rw [hT, Set.Finite.mem_toFinset]
      have hu' : valuation k (((u⁻¹ : kˣ) : k)) = 1 := by
        rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
      refine ⟨z * ((u⁻¹ : kˣ) : k), by
        show valuation k (z * ((u⁻¹ : kˣ) : k)) = 1
        rw [map_mul, hz, hu', mul_one], ?_⟩
      funext y
      simp [dilF, mul_assoc]
    · intro ψ _
      funext y
      simp [← mul_assoc]
    · intro ψ _
      funext y
      simp [← mul_assoc]
    · intro ψ _
      rfl

end GlobalTheory.PrinTwo
