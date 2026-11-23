import Mathlib

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.Conv

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

def conv (g : PowerSeries L) (f : ℤ → M) (k : ℤ) : M := ∑ᶠ j : ℕ, PowerSeries.coeff j g • f (k - j)

theorem conv_vanish (g : PowerSeries L) (f : ℤ → M) (m : ℤ) (hf : ∀ k < m, f k = 0) (e : ℕ)
    (hg : (PowerSeries.X : PowerSeries L) ^ e ∣ g) (k : ℤ) (hk : k < m + e) : conv g f k = 0 := by
  unfold conv
  rw [PowerSeries.X_pow_dvd_iff] at hg
  have hz : ∀ j : ℕ, PowerSeries.coeff j g • f (k - j) = 0 := by
    intro j
    by_cases hj : j < e
    · rw [hg j hj, zero_smul]
    · rw [hf _ (by omega), smul_zero]
  exact (finsum_congr hz).trans finsum_zero

theorem conv_lead (g : PowerSeries L) (f : ℤ → M) (m : ℤ) (hf : ∀ k < m, f k = 0) (e : ℕ)
    (hg : ∀ j < e, PowerSeries.coeff j g = 0) :
    conv g f (m + e) = PowerSeries.coeff e g • f m := by
  unfold conv
  rw [finsum_eq_single _ e]
  · rw [add_sub_cancel_right]
  · intro j hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hg j h, zero_smul]
    · rw [hf _ (by omega), smul_zero]

theorem triangular {ι : Type} [Fintype ι] (D : ι → ℤ → M) (m : ℤ) (hD : ∀ a, ∀ k < m, D a k = 0)
    (hind : LinearIndependent L (fun a => D a m)) (g : ι → PowerSeries L) (b : ℕ)
    (hsum : ∀ k < m + b, ∑ a, conv (g a) (D a) k = 0) :
    ∀ a, (PowerSeries.X : PowerSeries L) ^ b ∣ g a := by
  have key : ∀ n : ℕ, n < b → ∀ a, PowerSeries.coeff n (g a) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have h1 : ∑ a, PowerSeries.coeff n (g a) • D a m = 0 := by
        have hs := hsum (m + n) (by omega)
        calc ∑ a, PowerSeries.coeff n (g a) • D a m
            = ∑ a, conv (g a) (D a) (m + n) :=
              Finset.sum_congr rfl fun a _ =>
                (conv_lead (g a) (D a) m (hD a) n
                  (fun j hj => ih j hj (by omega) a)).symm
          _ = 0 := hs
      exact Fintype.linearIndependent_iff.mp hind (fun a => PowerSeries.coeff n (g a)) h1
  intro a
  rw [PowerSeries.X_pow_dvd_iff]
  intro n hn
  exact key n hn a

end Formalism.MainNotions.RamifiedCoefficientChains.S9.Conv
