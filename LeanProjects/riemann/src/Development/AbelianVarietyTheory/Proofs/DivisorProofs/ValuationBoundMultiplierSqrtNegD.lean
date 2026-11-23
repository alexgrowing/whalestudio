import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastAtEmbeddingRingOps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastBasicPropertiesStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.SzMult

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (σ p : ℂ), d.Prime → 4 < d → l ≠ d → Sz l lam 0 (12 * p) → Sz l lam 0 (-2 * (d : ℂ) * σ + ((d : ℂ) + 1) * p) → (l = 3 → d % 3 = 2) → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else 0) σ := by
  intro l _ lam d σ p hd hd4 hld hA hB h3
  have hlp : l.Prime := Fact.out
  obtain ⟨hint, -, hmul, hmono, -, hl, -⟩ := GlobalTheory.T.algebraicValuationAtLeast_basic_properties l lam
  obtain ⟨-, hadd2, -, -, hZ, -⟩ := GlobalTheory.QFam.SzSum.sz_ring l lam
  have hne : ∀ n : ℕ, ¬ l ∣ n → (n : ℂ) ≠ 0 := by
    intro n hn h
    apply hn
    rw [Nat.cast_eq_zero.mp h]
    exact dvd_zero l
  have hinv : ∀ n : ℕ, ¬ l ∣ n → Sz l lam 0 ((n : ℂ)⁻¹) := by
    intro n hn
    apply hint n _ hn
    rw [mul_inv_cancel₀ (hne n hn)]
    exact isIntegral_one
  have hnat : ∀ n : ℕ, Sz l lam 0 (n : ℂ) := fun n => by exact_mod_cast hZ n
  have hm0 : ∀ (r : ℝ) (x y : ℂ), Sz l lam 0 x → Sz l lam r y → Sz l lam r (x * y) := by
    intro r x y hx hy
    simpa using hmul 0 r x y hx hy
  have hcancel : ∀ (r : ℝ) (n : ℕ) (x : ℂ), ¬ l ∣ n → Sz l lam r ((n : ℂ) * x) → Sz l lam r x := by
    intro r n x hn h
    have := hm0 r _ _ (hinv n hn) h
    rwa [← mul_assoc, inv_mul_cancel₀ (hne n hn), one_mul] at this
  have hkey : ∀ r : ℝ, 0 ≤ r → Sz l lam r (((d : ℂ) + 1) * p) → Sz l lam r (((2 * d : ℕ) : ℂ) * σ) := by
    intro r hr h
    have hB' := hmono 0 r _ hr hB
    have := (hadd2 r _ _ h hB').2
    convert this using 1
    push_cast
    ring
  have hmulk : ∀ (r : ℝ) (m k : ℕ), d + 1 = m * k → Sz l lam r ((m : ℂ) * p) → Sz l lam r (((d : ℂ) + 1) * p) := by
    intro r m k hk h
    have := hm0 r (k : ℂ) _ (hnat k) h
    have e : ((d : ℂ) + 1) = (m : ℂ) * k := by exact_mod_cast hk
    rw [e]
    convert this using 1
    ring
  by_cases h2 : l = 2
  · subst h2
    have hd2 : ¬ 2 ∣ d := by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hd).mp h
      omega
    have h4p : Sz 2 lam 0 (((4 : ℕ) : ℂ) * p) := by
      apply hcancel 0 3 _ (by norm_num)
      convert hA using 1
      push_cast
      ring
    rw [if_pos rfl]
    split_ifs with h43
    · obtain ⟨k, hk⟩ : 4 ∣ d + 1 := by omega
      have h1 := hkey 0 le_rfl (hmulk 0 4 k hk h4p)
      have h2s : Sz 2 lam 0 (((2 : ℕ) : ℂ) * σ) := by
        apply hcancel 0 d _ hd2
        convert h1 using 1
        push_cast
        ring
      have := (hl 0 σ).mp h2s
      norm_num at this
      exact this
    · have h2p : Sz 2 lam 1 (((2 : ℕ) : ℂ) * p) := by
        have := (hl 0 (((2 : ℕ) : ℂ) * p)).mp (by convert h4p using 1; push_cast; ring)
        norm_num at this ⊢
        exact this
      obtain ⟨k, hk⟩ : 2 ∣ d + 1 := by omega
      have h1 := hkey 1 zero_le_one (hmulk 1 2 k hk h2p)
      have h2s : Sz 2 lam 1 (((2 : ℕ) : ℂ) * σ) := by
        apply hcancel 1 d _ hd2
        convert h1 using 1
        push_cast
        ring
      have := (hl 1 σ).mp h2s
      norm_num at this
      exact this
  · rw [if_neg h2]
    by_cases h3' : l = 3
    · subst h3'
      have hd3 := h3 rfl
      have h3p : Sz 3 lam 0 (((3 : ℕ) : ℂ) * p) := by
        apply hcancel 0 4 _ (by norm_num)
        convert hA using 1
        push_cast
        ring
      obtain ⟨k, hk⟩ : 3 ∣ d + 1 := by omega
      have h1 := hkey 0 le_rfl (hmulk 0 3 k hk h3p)
      exact hcancel 0 (2 * d) σ (by omega) h1
    · have hl2 : ∀ n : ℕ, n.Prime → l ∣ n → l = n := fun n hn h =>
        (Nat.prime_dvd_prime_iff_eq hlp hn).mp h
      have h12 : ¬ l ∣ 12 := by
        intro h
        rcases (Nat.Prime.dvd_mul hlp).mp (show l ∣ 2 * 2 * 3 from h) with h' | h'
        · rcases (Nat.Prime.dvd_mul hlp).mp h' with h'' | h'' <;>
            exact h2 (hl2 2 Nat.prime_two h'')
        · exact h3' (hl2 3 Nat.prime_three h')
      have h2d : ¬ l ∣ 2 * d := by
        intro h
        rcases (Nat.Prime.dvd_mul hlp).mp h with h' | h'
        · exact h2 (hl2 2 Nat.prime_two h')
        · exact hld (hl2 d hd h')
      have hp : Sz l lam 0 p := by
        apply hcancel 0 12 p h12
        exact_mod_cast hA
      have h1 := hkey 0 le_rfl (hmulk 0 1 (d + 1) (by ring) (by simpa using hp))
      exact hcancel 0 (2 * d) σ h2d h1

end GlobalTheory.SzMult
