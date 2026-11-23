import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.RowFixConj
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut

noncomputable section

open GlobalTheory.GLq GlobalTheory.Whittaker GlobalTheory.SmGL GlobalTheory.LocLanglands Matrix

namespace DiscreteGroups.sglob.DzFe

theorem lFE_of_fe : FunctionalEquationAtIndex → DzType.LFE := by
  intro hfe g _ m ψ₀ hψ τ hτ γ hγ l hl x hx
  have hfix : ∀ k, ∀ h : Gn g (m + 1),
      (∃ b : GL (Fin m) (ZMod g), (∀ i j : Fin m, i < j → (b : Matrix (Fin m) (Fin m) (ZMod g)) i j = 0) ∧
        corner b = cyc g (m + 1) ^ k * h * (cyc g (m + 1) ^ k)⁻¹) →
      τ.ρ h (τ.ρ (cyc g (m + 1) ^ k)⁻¹ x) = τ.ρ (cyc g (m + 1) ^ k)⁻¹ x := by
    rintro k h ⟨b, hb, hcb⟩
    have e : h * (cyc g (m + 1) ^ k)⁻¹ =
        (cyc g (m + 1) ^ k)⁻¹ * (cyc g (m + 1) ^ k * h * (cyc g (m + 1) ^ k)⁻¹) := by group
    calc τ.ρ h (τ.ρ (cyc g (m + 1) ^ k)⁻¹ x) = τ.ρ (h * (cyc g (m + 1) ^ k)⁻¹) x := by rw [map_mul]; rfl
      _ = τ.ρ ((cyc g (m + 1) ^ k)⁻¹ * corner b) x := by rw [e, ← hcb]
      _ = τ.ρ (cyc g (m + 1) ^ k)⁻¹ (τ.ρ (corner b) x) := by rw [map_mul]; rfl
      _ = τ.ρ (cyc g (m + 1) ^ k)⁻¹ x := by rw [hx b hb]
  have step : ∀ t, t < m → γ * l (τ.ρ (cyc g (m + 1) ^ t)⁻¹ x) =
      (g : ℂ) ^ ((m + 1) * m / 2 + (t + 1)) * l (τ.ρ (cyc g (m + 1) ^ (t + 1))⁻¹ x) := by
    intro t ht
    have hv : τ.ρ (cyc g (m + 1))⁻¹ (τ.ρ (cyc g (m + 1) ^ t)⁻¹ x) = τ.ρ (cyc g (m + 1) ^ (t + 1))⁻¹ x := by
      rw [pow_succ, _root_.mul_inv_rev, map_mul]; rfl
    have := hfe g m ψ₀ hψ τ hτ γ hγ l hl (m - 1 - t) (by omega) (τ.ρ (cyc g (m + 1) ^ t)⁻¹ x)
      (fun h hh => hfix t h (colFix_conj ht h hh)) (fun h hh => hfix t h (rowFix_conj ht h hh))
    rw [this, hv, show (m + 1) * m / 2 + m - (m - 1 - t) = (m + 1) * m / 2 + (t + 1) by omega]
  have key : ∀ t, t ≤ m → γ ^ t * l x =
      (g : ℂ) ^ (t * ((m + 1) * m / 2) + t * (t + 1) / 2) * l (τ.ρ (cyc g (m + 1) ^ t)⁻¹ x) := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
      have ih := ih (by omega)
      have h2 : (t + 1) * (t + 1 + 1) / 2 = t * (t + 1) / 2 + (t + 1) := by
        rw [show (t + 1) * (t + 1 + 1) = t * (t + 1) + 2 * (t + 1) by ring,
          Nat.add_mul_div_left _ _ (by norm_num)]
      have hE : t * ((m + 1) * m / 2) + t * (t + 1) / 2 + ((m + 1) * m / 2 + (t + 1)) =
          (t + 1) * ((m + 1) * m / 2) + (t + 1) * (t + 1 + 1) / 2 := by
        rw [h2]; ring
      calc γ ^ (t + 1) * l x = γ * (γ ^ t * l x) := by ring
        _ = γ * ((g : ℂ) ^ (t * ((m + 1) * m / 2) + t * (t + 1) / 2) * l (τ.ρ (cyc g (m + 1) ^ t)⁻¹ x)) := by
            rw [ih]
        _ = (g : ℂ) ^ (t * ((m + 1) * m / 2) + t * (t + 1) / 2) * (γ * l (τ.ρ (cyc g (m + 1) ^ t)⁻¹ x)) := by
            ring
        _ = (g : ℂ) ^ (t * ((m + 1) * m / 2) + t * (t + 1) / 2) *
            ((g : ℂ) ^ ((m + 1) * m / 2 + (t + 1)) * l (τ.ρ (cyc g (m + 1) ^ (t + 1))⁻¹ x)) := by
            rw [step t (by omega)]
        _ = _ := by rw [← mul_assoc, ← pow_add, hE]
  have hcm : (cyc g (m + 1) ^ m)⁻¹ = cyc g (m + 1) := by
    have h1 := cyc_pow_eq_one (g := g) m
    rw [pow_succ] at h1
    exact inv_eq_of_mul_eq_one_right h1
  have hfin := key m le_rfl
  rw [hcm] at hfin
  have hexp : m * (m + 1) ^ 2 / 2 = m * ((m + 1) * m / 2) + m * (m + 1) / 2 := by
    obtain ⟨r, hr⟩ := Nat.even_mul_succ_self m
    have h1 : (m + 1) * m / 2 = r := by rw [mul_comm, hr]; omega
    have h2 : m * (m + 1) / 2 = r := by rw [hr]; omega
    have h3 : m * (m + 1) ^ 2 / 2 = r * (m + 1) := by
      rw [show m * (m + 1) ^ 2 = 2 * (r * (m + 1)) by
        rw [show m * (m + 1) ^ 2 = m * (m + 1) * (m + 1) by ring, hr]; ring]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    rw [h1, h2, h3]; ring
  rw [longElt_corner_eq_cyc, hfin, hexp]

end DiscreteGroups.sglob.DzFe
