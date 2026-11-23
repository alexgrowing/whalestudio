import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ConjArith

theorem int_of_coprime_denoms (x : ℝ)
    (h : ∀ k : ℕ, 0 < k → ∃ b : ℕ, 0 < b ∧ Nat.Coprime b k ∧ ∃ n : ℤ, (b : ℝ) * x = n) :
    ∃ n : ℤ, x = n := by
  obtain ⟨b₁, hb₁, -, n₁, h₁⟩ := h 1 one_pos
  obtain ⟨b, hb, hcop, n, hn⟩ := h b₁ hb₁
  have hb₁R : (b₁ : ℝ) ≠ 0 := by exact_mod_cast hb₁.ne'
  have key : (n₁ : ℤ) * b = n * b₁ := by
    have : (n₁ : ℝ) * b = n * b₁ := by rw [← h₁, ← hn]; ring
    exact_mod_cast this
  have hdvd : (b₁ : ℤ) ∣ n₁ * b := ⟨n, by rw [key]; ring⟩
  have hc : IsCoprime (b₁ : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  obtain ⟨t, ht⟩ := hc.dvd_of_dvd_mul_right hdvd
  refine ⟨t, ?_⟩
  have : (b₁ : ℝ) * x = b₁ * t := by rw [h₁, ht]; push_cast; ring
  exact mul_left_cancel₀ hb₁R this

theorem int_core {S : Type} (m n : S → ℤ)
    (h : ∀ k : ℕ, 0 < k → ∃ a : ℤ, ∃ b : ℕ, Nat.Coprime b k ∧ IsCoprime a (k : ℤ) ∧
      ∀ s, (k : ℤ) ∣ n s - a * b * m s)
    (s₀ : S) (hm : m s₀ ≠ 0) (hpos : 0 < m s₀ * n s₀) : ∀ s, n s = m s := by
  have hn : n s₀ ≠ 0 := by
    rintro h0; rw [h0, mul_zero] at hpos; exact lt_irrefl _ hpos
  have h1 : m s₀ ∣ n s₀ := by
    obtain ⟨a, b, -, -, hk⟩ := h (m s₀).natAbs (Int.natAbs_pos.mpr hm)
    have h2 : ((m s₀).natAbs : ℤ) ∣ a * b * m s₀ :=
      Dvd.dvd.mul_left (Int.natAbs_dvd.mpr dvd_rfl) _
    have h3 := dvd_add (hk s₀) h2
    rw [sub_add_cancel] at h3
    exact Int.natAbs_dvd.mp h3
  have h2 : n s₀ ∣ m s₀ := by
    obtain ⟨a, b, hb, ha, hk⟩ := h (n s₀).natAbs (Int.natAbs_pos.mpr hn)
    have hself : ((n s₀).natAbs : ℤ) ∣ n s₀ := Int.natAbs_dvd.mpr dvd_rfl
    have h3 := dvd_sub hself (hk s₀)
    rw [sub_sub_cancel, _root_.mul_assoc] at h3
    have h4 : ((n s₀).natAbs : ℤ) ∣ b * m s₀ := ha.symm.dvd_of_dvd_mul_left h3
    have hbc : IsCoprime ((n s₀).natAbs : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hb.symm
    exact Int.natAbs_dvd.mp (hbc.dvd_of_dvd_mul_left h4)
  have heq : n s₀ = m s₀ := by
    have h5 := Int.natAbs_eq_of_dvd_dvd h1 h2
    rcases Int.natAbs_eq_natAbs_iff.mp h5 with h6 | h6
    · exact h6.symm
    · rw [h6] at hpos; nlinarith [mul_self_nonneg (m s₀)]
  intro s
  have hD : ∀ k : ℕ, 0 < k → (k : ℤ) ∣ n s * m s₀ - n s₀ * m s := by
    intro k hk
    obtain ⟨a, b, -, -, hks⟩ := h k hk
    have e : n s * m s₀ - n s₀ * m s
        = (n s - a * b * m s) * m s₀ - (n s₀ - a * b * m s₀) * m s := by ring
    rw [e]; exact dvd_sub ((hks s).mul_right _) ((hks s₀).mul_right _)
  have hD0 : n s * m s₀ - n s₀ * m s = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd (hD _ (Nat.succ_pos (n s * m s₀ - n s₀ * m s).natAbs))
    rw [Int.abs_eq_natAbs]; push_cast; omega
  rw [heq] at hD0
  have h7 : n s * m s₀ = m s * m s₀ := by linarith
  exact mul_right_cancel₀ hm h7

theorem form_eq_div : ∀ (S : Type) (f f' : S → ℝ) (A : ℝ), 0 < A → (∀ s, ∃ n : ℤ, f' s = n) →
    (∀ k : ℕ, 0 < k → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ Nat.Coprime b k ∧ IsCoprime a (k : ℤ) ∧
      ∀ s, (∃ n : ℤ, (b : ℝ) / A * f s = n) ∧ ∃ n : ℤ, f' s - a * ((b : ℝ) / A * f s) = k * n) →
    (∃ s, f s ≠ 0 ∧ 0 < f s * f' s) → ∀ s, f' s = f s / A := by
  intro S f f' A hA hint hk hex
  have hF : ∀ s, ∃ n : ℤ, f s / A = n := by
    intro s
    apply int_of_coprime_denoms
    intro k hk0
    obtain ⟨a, b, hb, hc, -, hs⟩ := hk k hk0
    obtain ⟨n, hn⟩ := (hs s).1
    exact ⟨b, hb, hc, n, by rw [← hn]; ring⟩
  choose m hm using hF
  choose n hn using hint
  have hcore : ∀ k : ℕ, 0 < k → ∃ a : ℤ, ∃ b : ℕ, Nat.Coprime b k ∧ IsCoprime a (k : ℤ) ∧
      ∀ s, (k : ℤ) ∣ n s - a * b * m s := by
    intro k hk0
    obtain ⟨a, b, -, hc, ha, hs⟩ := hk k hk0
    refine ⟨a, b, hc, ha, fun s => ?_⟩
    obtain ⟨t, ht⟩ := (hs s).2
    refine ⟨t, ?_⟩
    have : ((n s - a * b * m s : ℤ) : ℝ) = ((k * t : ℤ) : ℝ) := by
      push_cast
      rw [← hn s, ← ht, ← hm s]; ring
    exact_mod_cast this
  obtain ⟨s₀, hf0, hpos⟩ := hex
  have hmR : ((m s₀ : ℤ) : ℝ) * (n s₀ : ℝ) = f s₀ * f' s₀ / A := by
    rw [← hm s₀, ← hn s₀]; ring
  have hposZ : 0 < m s₀ * n s₀ := by
    have : (0 : ℝ) < ((m s₀ * n s₀ : ℤ) : ℝ) := by
      push_cast; rw [hmR]; exact div_pos hpos hA
    exact_mod_cast this
  have hm0 : m s₀ ≠ 0 := by
    rintro h0; rw [h0, zero_mul] at hposZ; exact lt_irrefl _ hposZ
  intro s
  rw [hn s, hm s]
  exact_mod_cast int_core m n hcore s₀ hm0 hposZ s

end GlobalTheory.ConjArith
