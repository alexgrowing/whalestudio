import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqSumBallFn

open ValuativeRel OnePoint GlobalTheory.LocGL.ProjLine

namespace GlobalTheory.LocGL.ProjLine

variable {k : Type} [Field k] [ValuativeRel k]

theorem Stable.scale_mem {S : Submodule ℂ (OnePoint k → ℂ)} (hS : Stable S) {c : k} (hc : c ≠ 0)
    (α β γ : ℂ) (a r b s : k)
    (h : α • (fun _ => (1 : ℂ)) + β • ballFn a r + γ • ballFn b s ∈ S) :
    α • (fun _ => (1 : ℂ)) + β • ballFn (c * a) (c * r) + γ • ballFn (c * b) (c * s) ∈ S := by
  have hv : 0 < valuation k c := zero_lt_iff.2 (by simpa using hc)
  have key : ∀ a r x : k, ballFn (c * a) (c * r) x = ballFn a r ((c⁻¹ * x + 0 : k) : OnePoint k) := by
    intro a r x
    have h1 : x - c * a = c * (c⁻¹ * x + 0 - a) := by field_simp; ring
    rw [ballFn_coe, ballFn_coe, h1, map_mul, map_mul]
    congr 1
    rw [mul_le_mul_iff_right₀ hv]
  refine hS.1 _ h c⁻¹ 0 (inv_ne_zero hc) _ (by simp) fun x => ?_
  simp only [Pi.add_apply, Pi.smul_apply, key]

theorem ballFn_eq_ballFn_zero {a r : k} (h : valuation k a ≤ valuation k r) : ballFn a r = ballFn 0 r := by
  funext x
  induction x using OnePoint.rec with
  | infty => rfl
  | coe x =>
    rw [ballFn_coe, ballFn_coe, sub_zero]
    congr 1
    refine propext ⟨fun hx => ?_, fun hx => (valuation k).map_sub_le hx h⟩
    have := (valuation k).map_add_le hx h
    rwa [sub_add_cancel] at this

theorem ballFn_congr_radius (a : k) {r s : k} (h : valuation k r = valuation k s) : ballFn a r = ballFn a s := by
  funext x
  induction x using OnePoint.rec with
  | infty => rfl
  | coe x => rw [ballFn_coe, ballFn_coe, h]

theorem Stable.ballFn_mem_and_one_mem_of_sub_mem (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (S : Submodule ℂ (OnePoint k → ℂ)) (hS : Stable S) (ϖ : k)
    (hϖ : valuation k ϖ = uniformizer k) (h : ballFn 0 ϖ - ballFn 1 ϖ ∈ S) :
    ballFn (0 : k) 1 ∈ S ∧ (fun _ => (1 : ℂ)) ∈ S := by
  classical
  have hlt : valuation k ϖ < 1 := hϖ ▸ uniformizer_lt_one
  have hle : ∀ x : k, valuation k x ≤ valuation k ϖ ↔ valuation k x < 1 := fun x => by
    rw [hϖ]; exact le_uniformizer_iff
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    exact uniformizer_ne_zero (hϖ.symm.trans (map_zero _))
  have hdiff : ∀ a : k, valuation k a ≤ 1 → ballFn 0 ϖ - ballFn a ϖ ∈ S := by
    intro a ha
    rcases ha.lt_or_eq with ha | ha
    · rw [ballFn_eq_ballFn_zero ((hle a).2 ha), sub_self]
      exact S.zero_mem
    · have ha0 : a ≠ 0 := by rintro rfl; simp at ha
      have h1 := hS.scale_mem ha0 0 1 (-1) 0 ϖ 1 ϖ (by simpa [sub_eq_add_neg] using h)
      have h2 : valuation k (a * ϖ) = valuation k ϖ := by rw [map_mul, ha, one_mul]
      rw [ballFn_congr_radius _ h2, ballFn_congr_radius _ h2] at h1
      simpa [sub_eq_add_neg] using h1
  obtain ⟨T, hT1, hT2, hT3⟩ := exists_eq_sum_ballFn (r := ϖ) (R := 1) h0 (by simpa using hlt.le)
  simp only [map_one] at hT1 hT2 hT3
  set q : ℂ := (T.card : ℂ) with hqdef
  have hsum : ballFn (0 : k) 1 = ∑ a ∈ T, ballFn a ϖ := by
    rw [hT3 (ballFn 0 1) rfl (fun x hx => by rw [ballFn_coe, if_neg (by simpa using hx)]) (fun x b hb => ?_)]
    · refine Finset.sum_congr rfl fun a ha => ?_
      rw [ballFn_coe, if_pos (by simpa using hT1 a ha), one_smul]
    · have hb1 : valuation k b ≤ 1 := hb.trans hlt.le
      rw [ballFn_coe, ballFn_coe, sub_zero, sub_zero, map_one]
      congr 1
      refine propext ⟨fun hx => ?_, fun hx => (valuation k).map_add_le hx hb1⟩
      have := (valuation k).map_sub_le hx hb1
      rwa [add_sub_cancel_right] at this
  set e : OnePoint k → ℂ := fun _ => 1 with he
  have R1 : (0 : ℂ) • e + (1 : ℂ) • ballFn (0 : k) 1 + (-q) • ballFn (0 : k) ϖ ∈ S := by
    have h1 := S.neg_mem (S.sum_mem fun a (ha : a ∈ T) => hdiff a (hT1 a ha))
    rw [Finset.sum_sub_distrib, ← hsum, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, ← hqdef] at h1
    convert h1 using 1
    module
  have R2 := hS.scale_mem h0 _ _ _ _ _ _ _ R1
  have R3 : (1 - q) • e + q • ballFn (0 : k) 1 + (-1 : ℂ) • ballFn (0 : k) ϖ ∈ S := by
    refine hS.2 _ R1 _ ?_ ?_ fun x hx => ?_
    · simp [ballFn_coe, he]; ring
    · simp [ballFn_coe, he]
    · have hx0 : 0 < valuation k x := zero_lt_iff.2 (by simpa using hx)
      simp only [Pi.add_apply, Pi.smul_apply, ballFn_coe, sub_zero, map_one, hϖ, le_uniformizer_iff, map_inv₀, he, smul_eq_mul,
        inv_le_one₀ hx0, inv_lt_one₀ hx0]
      rcases lt_trichotomy (valuation k x) 1 with h1 | h1 | h1
      · simp [h1, h1.le, h1.not_ge, h1.not_gt]
      · simp [h1]
      · simp [h1, h1.le, h1.not_ge, h1.not_gt]; ring
  have R4 := hS.scale_mem h0 _ _ _ _ _ _ _ R3
  simp only [mul_zero, mul_one] at R2 R4
  rw [← he] at R2 R4
  have hq1 : (1 - q) ≠ 0 := by
    rw [sub_ne_zero, hqdef]
    exact_mod_cast (hT2 hlt).ne
  have hq2 : (1 + q) ≠ 0 := by
    rw [hqdef]
    exact_mod_cast (by omega : 1 + T.card ≠ 0)
  have h2 : ballFn (0 : k) (ϖ * ϖ) ∈ S := by
    have h3 := S.sub_mem (S.add_mem (S.sub_mem R4 R3) (S.smul_mem q R1)) (S.smul_mem (q + 1 - q ^ 2) R2)
    have h4 : -((1 - q) * (1 - q) * (1 + q)) ≠ 0 := neg_ne_zero.2 (mul_ne_zero (mul_ne_zero hq1 hq1) hq2)
    refine (S.smul_mem_iff h4).1 ?_
    convert h3 using 1
    module
  have hu0 : ballFn (0 : k) 1 ∈ S := hS.ballFn_mem (mul_ne_zero h0 h0) h2 0 one_ne_zero
  have hu1 : ballFn (0 : k) ϖ ∈ S := hS.ballFn_mem (mul_ne_zero h0 h0) h2 0 h0
  refine ⟨hu0, (S.smul_mem_iff hq1).1 ?_⟩
  convert S.add_mem (S.sub_mem R3 (S.smul_mem q hu0)) hu1 using 1
  module

end GlobalTheory.LocGL.ProjLine
