import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit

section
open GlobalTheory.PsCo.PcEG

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

namespace GapNumber

theorem chain {r : ℕ} {lam : Fin r → ℤ} {H : ℤ} (hH : 0 ≤ H)
    (hg : ∀ i j : Fin r, (j : ℕ) = i + 1 → H ≤ lam i - lam j) :
    ∀ i j : Fin r, i < j → H ≤ lam i - lam j := by
  suffices h : ∀ (k : ℕ) (i j : Fin r), (j : ℕ) = i + k + 1 → H ≤ lam i - lam j by
    intro i j hij
    have : (i : ℕ) < j := hij
    exact h ((j : ℕ) - i - 1) i j (by omega)
  intro k
  induction k with
  | zero => intro i j h; exact hg i j (by omega)
  | succ k ih =>
    intro i j h
    have hm : (i : ℕ) + k + 1 < r := by have := j.isLt; omega
    have h1 := ih i ⟨(i : ℕ) + k + 1, hm⟩ rfl
    have h2 := hg ⟨(i : ℕ) + k + 1, hm⟩ j (by show (j : ℕ) = (i : ℕ) + k + 1 + 1; omega)
    linarith

end GapNumber

theorem gapConditions_of_largeGaps : GapNum := by
  intro r hr ε lam hg
  obtain ⟨k, hk⟩ := hr
  have hr1 : 1 ≤ r := by omega
  have hH : (0 : ℤ) ≤ 100 * (r : ℤ) ^ 4 := by positivity
  have hc := GapNumber.chain hH hg
  have hcR : ∀ i j : Fin r, i < j → 100 * (r : ℝ) ^ 4 ≤ (lam i : ℝ) - lam j := fun i j h => by
    exact_mod_cast hc i j h
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hpos : (0 : ℝ) < 100 * (r : ℝ) ^ 4 := by positivity
  have hanti : StrictAnti (fun a => (lam a : ℝ)) := fun i j h => by
    have := hcR i j h
    show (lam j : ℝ) < lam i
    linarith
  have hgap : GapAtLeast ε (fun a => (lam a : ℝ)) (100 * (r : ℝ) ^ 4) := by
    intro a b hab
    have hne : a ≠ b := fun h => hab (h ▸ rfl)
    show 100 * (r : ℝ) ^ 4 ≤ |(lam a : ℝ) - lam b|
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hcR a b h).trans (le_abs_self _)
    · rw [abs_sub_comm]; exact (hcR b a h).trans (le_abs_self _)
  have hp : pOf ε ≤ r := (Finset.card_filter_le _ _).trans_eq (by simp)
  have hq : qOf ε ≤ r := (Finset.card_filter_le _ _).trans_eq (by simp)
  have hq0 : S7.q0 ε ≤ r := (min_le_left _ _).trans hp
  have hpR : (pOf ε : ℝ) ≤ r := by exact_mod_cast hp
  have hqR : (qOf ε : ℝ) ≤ r := by exact_mod_cast hq
  have hq0R : (S7.q0 ε : ℝ) ≤ r := by exact_mod_cast hq0
  have h1 : (1 : ℝ) ≤ (r : ℝ) ^ 4 := one_le_pow₀ hrR
  have h4 : (r : ℝ) ≤ (r : ℝ) ^ 4 := le_self_pow₀ hrR (by norm_num)
  have h2 : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 4 := pow_le_pow_right₀ hrR (by norm_num)
  have h3 : (r : ℝ) ^ 3 ≤ (r : ℝ) ^ 4 := pow_le_pow_right₀ hrR (by norm_num)
  have hbig : (r : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < 100 * (r : ℝ) ^ 4 := by
    have : (r : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤ r * r * r := by gcongr
    nlinarith
  refine ⟨⟨hanti, fun a => ⟨lam a - k, ?_⟩⟩, ⟨hanti, _, hgap, hbig⟩, ⟨hanti, _, hgap, by linarith⟩, _, hgap, ?_⟩
  · have hkR : (r : ℝ) = 2 * k + 1 := by exact_mod_cast hk
    show (lam a : ℝ) - ((r : ℝ) - 1) / 2 = ((lam a - k : ℤ) : ℝ)
    rw [hkR]; push_cast; ring
  · unfold thrStar
    refine max_lt hbig ?_
    have hs : Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ 2 * r := by
      rw [show (2 : ℝ) * r = Real.sqrt ((2 * r) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hm : (r : ℝ) * (S7.q0 ε : ℝ) ≤ r * r := mul_le_mul_of_nonneg_left hq0R (by positivity)
    nlinarith

end GlobalTheory.PsCo.PcEF

end
end
