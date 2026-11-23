import Mathlib
import Formalism.MirabolicMackeyTheory.StatementT
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

def OnExport2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ), 0 < D →
  ∀ (Tup : Type) (μ : HeightOneSpectrum (𝓞 K) → Tup) (J : Type) [Fintype J] (d : J → ℕ),
    (∀ j, d j = D) →
  ∀ (M : ∀ j, Submodule (𝓞 K) (Fin (d j) → K))
    (T : ∀ j, Tup → Submodule (𝓞 K) (Fin (d j) → K))
    (θ : ∀ j, Tup → Matrix (Fin (d j)) (Fin (d j)) K)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (e0 r0 ε0 F0 errl Jx : HeightOneSpectrum (𝓞 K) → J → ℝ)
    (vU0 gq : HeightOneSpectrum (𝓞 K) → ℝ) (dK EA Rb EJ : J → ℝ) (δq E3 : ℝ), 0 < δq →
    (∀ w ∈ S, ∀ j, (idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) ≤
      (ramw w : ℝ) * ((e0 w j + vU0 w) * (d j : ℝ) + (r0 w j + dK j * vU0 w) / δq + ε0 w j)) →
    (∀ w ∈ S, ∀ j, (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) ≤
      (ramw (conjPl w) : ℝ) * ((e0 (conjPl w) j + vU0 (conjPl w)) * (d j : ℝ) +
        (r0 (conjPl w) j + dK j * vU0 (conjPl w)) / δq + ε0 (conjPl w) j)) →
    (∀ j, dK j / δq ≤ 3 * (D : ℝ)) →
    (∀ w ∈ S, 0 ≤ vU0 w ∧ vU0 (conjPl w) = vU0 w ∧ 4 * vU0 w ≤ gq w) →
    (∀ w ∈ S, ∀ j, e0 w j + e0 (conjPl w) j - 2 * F0 w j + 2 * gq w ≤ errl w j) →
    (∀ w ∈ S, ∑ j, (ε0 w j + ε0 (conjPl w) j) ≤ 2 / (plc w : ℝ) ^ 2) →
    (∀ j, ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w j) ≤ EA j) →
    (∀ j, ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), ∑ w ∈ S', lw w * ((ramw w : ℝ) * r0 w j) ≤ Rb j) →
    (∀ j, ∑ w ∈ S, lw w * Jx w j ≤ EJ j) →
    ∑ w ∈ S, lw w * ((ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2)) ≤ E3 →
      (∀ w ∈ S, ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
          (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ)) ≤
        (∑ j, (2 * ((ramw w : ℝ) * F0 w j) +
            (ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)))) +
          2 / ellw w ^ 2) * D) ∧
      (∀ j, ∑ w ∈ S, lw w * ((ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ))) +
          Jx w j) ≤ EA j + 2 * Rb j / (δq * (D : ℝ)) + EJ j) ∧
      ∑ w ∈ S, lw w * (2 / ellw w ^ 2) ≤ E3

theorem onExport2_of (hR : RamBasic) : OnExport2 := by
  classical
  intro K _ _ _ D hD Tup μ J _ d hd M T θ S e0 r0 ε0 F0 errl Jx vU0 gq dK EA Rb EJ δq E3 hδ h1 h2 hsh hv
    hdep htw hEA hRb hEJ hE3
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨hp, hr1, hpc, hrc, hell⟩ := hR K w
    have hρ : (1 : ℝ) ≤ (ramw w : ℝ) := by exact_mod_cast hr1
    obtain ⟨hv0, hvc, hvg⟩ := hv w hw
    have hl : (0 : ℝ) < (plc w : ℝ) ^ 2 := by
      have : (0 : ℝ) < (plc w : ℝ) := by exact_mod_cast hp.pos
      positivity
    have key : ∀ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
          (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ)) ≤
        (2 * ((ramw w : ℝ) * F0 w j) +
            (ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)))) * D +
          (ramw w : ℝ) * (ε0 w j + ε0 (conjPl w) j) := by
      intro j
      have a1 := h1 w hw j
      have a2 := h2 w hw j
      rw [hrc, hvc] at a2
      have hdj : (d j : ℝ) = D := by exact_mod_cast hd j
      rw [hdj] at a1 a2
      have a3 := hdep w hw j
      have a4 := hsh j
      have e1 : (r0 w j + dK j * vU0 w) / δq = r0 w j / δq + dK j / δq * vU0 w := by
        field_simp
      have e2 : (r0 (conjPl w) j + dK j * vU0 w) / δq = r0 (conjPl w) j / δq + dK j / δq * vU0 w := by
        field_simp
      have e3 : (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)) * D = r0 w j / δq + r0 (conjPl w) j / δq := by
        field_simp
      rw [e1] at a1
      rw [e2] at a2
      have b1 : dK j / δq * vU0 w ≤ 3 * (D : ℝ) * vU0 w := mul_le_mul_of_nonneg_right a4 hv0
      have b2 : (e0 w j + e0 (conjPl w) j + 8 * vU0 w) * (D : ℝ) ≤ (2 * F0 w j + errl w j) * D :=
        mul_le_mul_of_nonneg_right (by linarith) hDr.le
      have b3 : ((e0 w j + vU0 w) * (D : ℝ) + (r0 w j / δq + dK j / δq * vU0 w) + ε0 w j) +
          ((e0 (conjPl w) j + vU0 w) * (D : ℝ) + (r0 (conjPl w) j / δq + dK j / δq * vU0 w) +
            ε0 (conjPl w) j) ≤
          (2 * F0 w j + errl w j) * D + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)) * D +
            (ε0 w j + ε0 (conjPl w) j) := by
        rw [e3]; nlinarith
      have b4 := mul_le_mul_of_nonneg_left b3 (by linarith : (0 : ℝ) ≤ (ramw w : ℝ))
      calc _ ≤ _ := add_le_add a1 a2
        _ = (ramw w : ℝ) * (((e0 w j + vU0 w) * (D : ℝ) + (r0 w j / δq + dK j / δq * vU0 w) + ε0 w j) +
          ((e0 (conjPl w) j + vU0 w) * (D : ℝ) + (r0 (conjPl w) j / δq + dK j / δq * vU0 w) +
            ε0 (conjPl w) j)) := by ring
        _ ≤ _ := b4
        _ = _ := by ring
    calc _ ≤ _ := Finset.sum_le_sum (fun j _ => key j)
      _ = (∑ j, (2 * ((ramw w : ℝ) * F0 w j) +
            (ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ))))) * D +
          (ramw w : ℝ) * ∑ j, (ε0 w j + ε0 (conjPl w) j) := by
            rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      _ ≤ _ := by
        rw [hell, add_mul]
        have c1 := mul_le_mul_of_nonneg_left (htw w hw) (by linarith : (0 : ℝ) ≤ (ramw w : ℝ))
        have c2 : (ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2) ≤ (ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2) * D := by
          have c3 : (0 : ℝ) ≤ (ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2) := by positivity
          nlinarith
        linarith
  · intro j
    have hc : ∑ w ∈ S, lw w * ((ramw w : ℝ) * r0 (conjPl w) j) ≤ Rb j := by
      have hinj : Set.InjOn (conjPl (K := K)) S := by
        intro a _ b _ hab
        have := congrArg conjPl hab
        rwa [(valuation_basic_properties K a).2.2.2.1, (valuation_basic_properties K b).2.2.2.1] at this
      have := hRb j (S.image conjPl)
      rw [Finset.sum_image hinj] at this
      refine le_trans (le_of_eq ?_) this
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [(valuation_basic_properties K w).2.2.1, (hR K w).2.2.2.1]
    have hpos : (0 : ℝ) < δq * D := mul_pos hδ hDr
    have e : ∑ w ∈ S, lw w * ((ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ))) +
          Jx w j) =
        ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w j) +
          (∑ w ∈ S, lw w * ((ramw w : ℝ) * r0 w j) + ∑ w ∈ S, lw w * ((ramw w : ℝ) * r0 (conjPl w) j)) /
            (δq * (D : ℝ)) + ∑ w ∈ S, lw w * Jx w j := by
      rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      ring
    rw [e]
    have f1 : (∑ w ∈ S, lw w * ((ramw w : ℝ) * r0 w j) +
        ∑ w ∈ S, lw w * ((ramw w : ℝ) * r0 (conjPl w) j)) / (δq * (D : ℝ)) ≤ 2 * Rb j / (δq * (D : ℝ)) :=
      div_le_div_of_nonneg_right (by linarith [hRb j S]) hpos.le
    linarith [hEA j, hEJ j]
  · refine le_trans (le_of_eq ?_) hE3
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [(hR K w).2.2.2.2]

theorem local_conditions_global_form : OnExport2 := onExport2_of ramified_basic_bound

end Formalism.EigenvalueLevelCeiling
