import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartFormsAlt

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [DecidableEq ι] in

theorem chartMonomial_add (c : (k : ι) → Fin (n k + 1)) (e e' : ι → ℕ) :
    chartMonomial c (e + e') = chartMonomial c e * chartMonomial c e' := by
  simp [chartMonomial, pow_add, Finset.prod_mul_distrib]

omit [DecidableEq ι] in

theorem chartMonomial_zero (c : (k : ι) → Fin (n k + 1)) :
    chartMonomial c (0 : ι → ℕ) = 1 := by
  simp [chartMonomial]

theorem chartMonomial_single (c : (k : ι) → Fin (n k + 1)) (k : ι) :
    chartMonomial c (Pi.single k 1) = X ⟨k, c k⟩ := by
  rw [chartMonomial, Finset.prod_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem mkF_chartMonomial (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) (e : ι → ℕ) :
    P.mkF (chartMonomial c e) = ∏ k, P.mkF (X ⟨k, c k⟩) ^ e k := by
  simp [chartMonomial, map_prod, map_pow]

theorem exists_form_of_mem_chartRing (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1))
    (hc : P.IsLive c) {x : P.FunField} (hx : x ∈ P.chartRing c) :
    ∃ (F : MvPolynomial (Coord n) ℤ) (e : ι → ℕ), IsWeightedHomogeneous (coordDeg n) F e ∧
      x * P.mkF (chartMonomial c e) = P.mkF F := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    have hne : P.mkF (X ⟨v.1, c v.1⟩) ≠ 0 := fun h ↦ hc v.1 ((P.mkF_eq_zero_iff _).mp h)
    refine ⟨X v, Pi.single v.1 1, ?_, ?_⟩
    · have h := isWeightedHomogeneous_X (R := ℤ) (coordDeg n) v
      simpa [coordDeg] using h
    · rw [chartMonomial_single, ArithVariety.chartCoord, div_mul_cancel₀ _ hne]
  | zero => exact ⟨0, 0, isWeightedHomogeneous_zero _ _ _, by simp⟩
  | one => exact ⟨1, 0, isWeightedHomogeneous_one _ _, by simp [chartMonomial_zero]⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨F, e, hF, hxF⟩ := ihx
    obtain ⟨F', e', hF', hyF⟩ := ihy
    refine ⟨F * chartMonomial c e' + F' * chartMonomial c e, e + e', ?_, ?_⟩
    · refine (hF.mul (isWeightedHomogeneous_chartMonomial c e')).add ?_
      rw [add_comm e e']
      exact hF'.mul (isWeightedHomogeneous_chartMonomial c e)
    · rw [chartMonomial_add, map_add, map_mul, map_mul, map_mul, ← hxF, ← hyF]
      ring
  | neg x _ ih =>
    obtain ⟨F, e, hF, hxF⟩ := ih
    exact ⟨-F, e, hF.neg, by rw [map_neg, ← hxF, neg_mul]⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨F, e, hF, hxF⟩ := ihx
    obtain ⟨F', e', hF', hyF⟩ := ihy
    refine ⟨F * F', e + e', hF.mul hF', ?_⟩
    rw [chartMonomial_add, map_mul, map_mul, ← hxF, ← hyF]
    ring

end ChartFormsAlt

open ChartFormsAlt in

theorem ChartFormsAlt.proof : ChartFormsAlt.Statement := by
  classical
  intro ι _ _ n P D
  have hrep : ∀ (c : (k : ι) → Fin (n k + 1)) (j : Fin (D.size + 1)),
      ∃ (F : MvPolynomial (Coord n) ℤ) (e : ι → ℕ), IsWeightedHomogeneous (coordDeg n) F e ∧
        (P.IsLive c → D.elt j / P.chartPow c D.deg * P.mkF (chartMonomial c e) = P.mkF F) := by
    intro c j
    by_cases hc : P.IsLive c
    · obtain ⟨F, e, hF, h⟩ := exists_form_of_mem_chartRing P c hc (D.chart_mem c hc j)
      exact ⟨F, e, hF, fun _ ↦ h⟩
    · exact ⟨0, 0, isWeightedHomogeneous_zero _ _ _, fun h ↦ absurd h hc⟩
  choose F e hF hFe using hrep
  refine ⟨fun k ↦ 1 + (∑ c, ∑ j, e c j k) + (-D.deg k).toNat, fun d hd ↦ ?_⟩
  have hle : ∀ c j k, e c j k ≤ ∑ c, ∑ j, e c j k := fun c j k ↦
    (Finset.single_le_sum (f := fun j ↦ e c j k) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun c ↦ ∑ j, e c j k) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ c))
  have hdk : ∀ k, 1 + (∑ c, ∑ j, e c j k) + (-D.deg k).toNat ≤ d k := fun k ↦ hd k
  have ht : ∀ c j k, (e c j k : ℤ) ≤ d k + D.deg k := by
    intro c j k
    have h1 := hle c j k
    have h2 := hdk k
    omega
  have hnn : ∀ k, 0 ≤ (d k : ℤ) + D.deg k := by
    intro k
    have h2 := hdk k
    omega
  let t : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → ι → ℕ :=
    fun c j k ↦ ((d k : ℤ) + D.deg k - e c j k).toNat
  refine ⟨fun c j ↦ if P.IsLive c then F c j * chartMonomial c (t c j) else 0, ?_⟩
  refine ⟨fun k ↦ ?_, hnn, fun c j ↦ ?_, fun c hc j ↦ ?_, fun c hc j ↦ ?_⟩
  · have h2 := hdk k
    omega
  · refine ⟨fun k ↦ ((d k : ℤ) + D.deg k).toNat, ?_, fun k ↦ Int.toNat_of_nonneg (hnn k)⟩
    split_ifs with hc
    · have hd' : e c j + t c j = fun k ↦ ((d k : ℤ) + D.deg k).toNat := by
        funext k
        have h1 := ht c j k
        simp only [Pi.add_apply, t]
        omega
      rw [← hd']
      exact (hF c j).mul (isWeightedHomogeneous_chartMonomial c (t c j))
    · exact isWeightedHomogeneous_zero _ _ _
  · simp only [if_pos hc]
    have hy : ∀ k, P.mkF (X ⟨k, c k⟩) ≠ 0 := fun k h ↦ hc k ((P.mkF_eq_zero_iff _).mp h)
    have hC : P.chartPow c D.deg ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (hy k)
    have key : P.mkF (chartMonomial c (e c j)) * P.mkF (chartMonomial c (t c j)) =
        P.mkF (chartMonomial c d) * P.chartPow c D.deg := by
      rw [mkF_chartMonomial, mkF_chartMonomial, mkF_chartMonomial, ArithVariety.chartPow,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k), ← zpow_add₀ (hy k)]
      congr 1
      have h1 := ht c j k
      simp only [t]
      omega
    rw [map_mul, ← hFe c j hc, mul_assoc, key]
    field_simp
  · simp [if_neg hc]

end

end GroundTheory.Heights₂.Heights
