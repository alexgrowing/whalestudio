import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutOutSubgroupTangentSecondOrderHilbertSchmidtStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem slab_arith_lower {a s r t η u v : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hst : s < t) (hrt : r < t)
    (ht : t ≤ 1 / 24) (hη : 0 < η) (htη : 3 * t * (1 + η) ≤ η) (h1 : a < 1 / 8 + s + a * s)
    (h2 : a ≤ u + a ^ 2) (h3 : u ≤ v + a * s) (h4 : v ≤ r) : a ≤ (1 + η) * r := by

  have hs24 : s < 1 / 24 := lt_of_lt_of_le hst ht
  have hA : a < 4 / 23 := by nlinarith [mul_nonneg ha (sub_nonneg.2 hs24.le)]
  have hkey : a * (1 - s - a) ≤ r := by nlinarith
  have hgap : 433 / 552 ≤ 1 - s - a := by linarith
  have hat : a * (433 / 552) < t := by nlinarith [mul_le_mul_of_nonneg_left hgap ha]
  have hsum : (1 + η) * (s + a) ≤ η := by
    nlinarith [mul_le_mul_of_nonneg_left (show s + a ≤ 3 * t by linarith) (show (0 : ℝ) ≤ 1 + η by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hkey (show (0 : ℝ) ≤ 1 + η by linarith),
    mul_le_mul_of_nonneg_left hsum ha]

theorem slab_squeeze : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → ∀ ρ η : ℝ, 0 < ρ → ρ ≤ 1 / 8 → 0 < η →
    ∃ t : ℝ, 0 < t ∧ ∀ r : ℝ, 0 < r → r < t → ∀ k : Formalism.REAL.UJ ε, nrm (uMat k - 1) < t →
      crd E (uMat k - 1) = 0 → ∀ l ∈ S, (l ∈ hsBall ε (r / (1 + η)) → l * k ∈ slab ε E ρ r) ∧
        (l * k ∈ slab ε E ρ r → l ∈ hsBall ε ((1 + η) * r)) := by
  intro n ε S d E hS ρ η hρ hρ8 hη
  have hON := hS.isON
  obtain ⟨t, ht0, ht24, htη, htρ⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 24 ∧ 3 * t * (1 + η) ≤ η ∧ 3 * t ≤ ρ := by
    refine ⟨min (1 / 24) (min (η / (3 * (1 + η))) (ρ / 3)),
      lt_min (by norm_num) (lt_min (by positivity) (by positivity)), min_le_left _ _, ?_, ?_⟩
    · have h : min (1 / 24) (min (η / (3 * (1 + η))) (ρ / 3)) * (3 * (1 + η)) ≤ η :=
        (le_div_iff₀ (by positivity)).1 (le_trans (min_le_right _ _) (min_le_left _ _))
      linarith
    · have h := le_trans (min_le_right (1 / 24 : ℝ) _) (min_le_right (η / (3 * (1 + η))) (ρ / 3))
      linarith
  refine ⟨t, ht0, ?_⟩
  intro r hr hrt k hk hk0 l hl

  have hmul : uMat (l * k) - 1 = (uMat l - 1) + (uMat k - 1) + (uMat l - 1) * (uMat k - 1) := by
    have e : uMat (l * k) = uMat l * uMat k := rfl
    rw [e]; noncomm_ring
  have hXY : nrm ((uMat l - 1) * (uMat k - 1)) ≤ nrm (uMat l - 1) * nrm (uMat k - 1) := nrm_mul_le _ _
  have ha0 := nrm_nonneg (uMat l - 1)
  have hs0 := nrm_nonneg (uMat k - 1)
  have htle : t ≤ η := by nlinarith
  constructor
  · intro hlB
    have ha : nrm (uMat l - 1) ≤ r / (1 + η) := hlB
    have ha' : nrm (uMat l - 1) * (1 + η) ≤ r := (le_div_iff₀ (by positivity)).1 ha
    refine ⟨?_, ?_⟩
    ·
      have h1 : nrm (uMat (l * k) - 1) ≤ nrm (uMat l - 1) + nrm (uMat k - 1) + nrm ((uMat l - 1) * (uMat k - 1)) := by
        rw [hmul]
        exact le_trans (nrm_add_le _ _) (by linarith [nrm_add_le (uMat l - 1) (uMat k - 1)])
      have hat : nrm (uMat l - 1) < t := by nlinarith
      have hprod : nrm (uMat l - 1) * nrm (uMat k - 1) ≤ t * t := by
        exact mul_le_mul hat.le hk.le hs0 ht0.le
      nlinarith
    ·
      have hc : crd E (uMat (l * k) - 1) = crd E (uMat l - 1) + crd E ((uMat l - 1) * (uMat k - 1)) := by
        rw [hmul, crd_add, crd_add, hk0, add_zero]
      have hlen : len (crd E (uMat (l * k) - 1)) ≤ nrm (uMat l - 1) + nrm (uMat l - 1) * nrm (uMat k - 1) := by
        rw [hc]
        exact le_trans (len_add_le _ _)
          (add_le_add (len_crd_le hON _) (le_trans (len_crd_le hON _) hXY))
      have hsη : nrm (uMat l - 1) * nrm (uMat k - 1) ≤ nrm (uMat l - 1) * η :=
        mul_le_mul_of_nonneg_left (by linarith) ha0
      show len (crd E (uMat (l * k) - 1)) ≤ r
      nlinarith
  · intro hslab
    obtain ⟨hZ, hv⟩ := hslab
    show nrm (uMat l - 1) ≤ (1 + η) * r
    have hX : uMat l - 1 = (uMat (l * k) - 1) - (uMat k - 1) - (uMat l - 1) * (uMat k - 1) := by
      rw [hmul]; abel

    have h1 : nrm (uMat l - 1) < 1 / 8 + nrm (uMat k - 1) + nrm (uMat l - 1) * nrm (uMat k - 1) := by
      have e := nrm_sub_le ((uMat (l * k) - 1) - (uMat k - 1)) ((uMat l - 1) * (uMat k - 1))
      have e' := nrm_sub_le (uMat (l * k) - 1) (uMat k - 1)
      rw [← hX] at e
      linarith

    have h2 : nrm (uMat l - 1) ≤ len (crd E (uMat l - 1)) + nrm (uMat l - 1) ^ 2 := by
      have hp := GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt n ε S d E hS l hl
      have e := nrm_add_le (cmb E (crd E (uMat l - 1))) (uMat l - 1 - cmb E (crd E (uMat l - 1)))
      rw [add_sub_cancel, nrm_cmb hON] at e
      linarith

    have h3 : len (crd E (uMat l - 1)) ≤ len (crd E (uMat (l * k) - 1)) + nrm (uMat l - 1) * nrm (uMat k - 1) := by
      have hc : crd E (uMat l - 1) = crd E (uMat (l * k) - 1) + -crd E ((uMat l - 1) * (uMat k - 1)) := by
        conv_lhs => rw [hX]
        rw [crd_sub, crd_sub, hk0, sub_zero, sub_eq_add_neg]
      rw [hc]
      refine le_trans (len_add_le _ _) (add_le_add le_rfl ?_)
      rw [len_neg]
      exact le_trans (len_crd_le hON _) hXY
    exact slab_arith_lower ha0 hs0 hk hrt ht24 hη htη (by linarith) h2 h3 hv

end GlobalTheory.IwConst
