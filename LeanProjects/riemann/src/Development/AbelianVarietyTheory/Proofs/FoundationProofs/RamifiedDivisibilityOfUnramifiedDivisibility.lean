import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral
open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem GlobalTheory.KZ.ramified_divisible_of_unramified : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (v : Valuation Ω ℝ≥0) (ψ : O0 p →+* Ω) (E F : ℕ) (π : Ω) (κ : Fin F → Ω), 1 ≤ E → 0 < v (p : Ω) → v (p : Ω) < 1 → v π ^ E = v (p : Ω) → (∀ j, v (κ j) ≤ 1) → (∀ y, v (ψ y) ≤ 1) → (∀ b : Fin F → Lau p, v (∑ j, κ j * ψ (algebraMap (Lau p) (O0 p) (b j))) < 1 → ∀ j, (p : Lau p) ∣ b j) → ∀ b : Fin F → Fin E → Lau p, v (∑ j, ∑ s : Fin E, κ j * π ^ (s : ℕ) * ψ (algebraMap (Lau p) (O0 p) (b j s))) ≤ v (p : Ω) → ∀ j s, (p : Lau p) ∣ b j s := by
  intro p _ Ω _ _ v ψ E F π κ hE hp0 hp1 hπE hκ hψ hunr b htot
  classical
  set a := algebraMap (Lau p) (O0 p) with ha
  set Y : Fin E → Ω := fun s => ∑ j, κ j * ψ (a (b j s)) with hY
  have hsum : (∑ j, ∑ s : Fin E, κ j * π ^ (s : ℕ) * ψ (a (b j s)))
      = ∑ s : Fin E, π ^ (s : ℕ) * Y s := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hY, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsum] at htot

  have hπpos : 0 < v π := by
    rcases eq_or_ne (v π) 0 with h | h
    · exfalso
      have : v π ^ E = 0 := by rw [h]; exact zero_pow (by omega)
      rw [hπE] at this; exact absurd this hp0.ne'
    · exact pos_iff_ne_zero.mpr h
  have hπ1 : v π < 1 := by
    by_contra h
    replace h := not_lt.mp h
    have : 1 ≤ v π ^ E := one_le_pow₀ h
    rw [hπE] at this
    exact absurd hp1 (not_lt.mpr this)
  have hπle : v π ≤ 1 := hπ1.le
  have hY1 : ∀ s, v (Y s) ≤ 1 := by
    intro s
    refine Valuation.map_sum_le v (fun j _ => ?_)
    rw [map_mul]
    calc v (κ j) * v (ψ (a (b j s))) ≤ 1 * 1 := mul_le_mul' (hκ j) (hψ _)
      _ = 1 := one_mul 1
  have hYp : ∀ s, (∀ j, (p : Lau p) ∣ b j s) → v (Y s) ≤ v (p : Ω) := by
    intro s hs
    refine Valuation.map_sum_le v (fun j _ => ?_)
    obtain ⟨c, hc⟩ := hs j
    rw [hc, map_mul, map_mul, map_natCast, map_mul, map_natCast, map_mul]
    calc v (κ j) * (v (p : Ω) * v (ψ (a c))) ≤ 1 * (v (p : Ω) * 1) :=
          mul_le_mul' (hκ j) (mul_le_mul' le_rfl (hψ _))
      _ = v (p : Ω) := by rw [one_mul, mul_one]
  have step : ∀ s : Fin E, (∀ s' : Fin E, s' < s → ∀ j, (p : Lau p) ∣ b j s') →
      ∀ j, (p : Lau p) ∣ b j s := by
    intro s ih
    have hsE : (s : ℕ) + 1 ≤ E := s.isLt
    have hpB : v (p : Ω) ≤ v π ^ ((s : ℕ) + 1) := by
      rw [← hπE]; exact pow_le_pow_of_le_one zero_le hπle hsE
    have hrest : v (∑ s' ∈ Finset.univ.erase s, π ^ (s' : ℕ) * Y s') ≤ v π ^ ((s : ℕ) + 1) := by
      refine Valuation.map_sum_le v (fun s' hs' => ?_)
      have hne : s' ≠ s := Finset.ne_of_mem_erase hs'
      rw [map_mul, map_pow]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · calc v π ^ (s' : ℕ) * v (Y s') ≤ 1 * v (p : Ω) :=
              mul_le_mul' (pow_le_one₀ zero_le hπle) (hYp s' (ih s' hlt))
          _ ≤ v π ^ ((s : ℕ) + 1) := by rw [one_mul]; exact hpB
      · have hgt' : (s : ℕ) + 1 ≤ (s' : ℕ) := hgt
        calc v π ^ (s' : ℕ) * v (Y s') ≤ v π ^ (s' : ℕ) * 1 := mul_le_mul' le_rfl (hY1 s')
          _ = v π ^ (s' : ℕ) := mul_one _
          _ ≤ v π ^ ((s : ℕ) + 1) := pow_le_pow_of_le_one zero_le hπle hgt'
    have hsplit : π ^ (s : ℕ) * Y s
        = (∑ s' : Fin E, π ^ (s' : ℕ) * Y s') - ∑ s' ∈ Finset.univ.erase s, π ^ (s' : ℕ) * Y s' := by
      rw [← Finset.add_sum_erase Finset.univ (fun s' : Fin E => π ^ (s' : ℕ) * Y s')
        (Finset.mem_univ s)]
      ring
    have hmain : v (π ^ (s : ℕ) * Y s) ≤ v π ^ ((s : ℕ) + 1) := by
      rw [hsplit]
      refine (Valuation.map_sub v _ _).trans (max_le (htot.trans hpB) hrest)
    rw [map_mul, map_pow, pow_succ] at hmain
    have hYs : v (Y s) ≤ v π :=
      le_of_mul_le_mul_left hmain (pow_pos hπpos _)
    exact hunr (fun j => b j s) (lt_of_le_of_lt hYs hπ1)
  intro j s
  exact WellFoundedLT.induction s (fun s ih => step s ih) j
