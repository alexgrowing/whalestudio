import Formalism.MahlerMeasure.LevelDecompR
import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelAct

namespace Formalism.GM

open MvPolynomial Finset

section
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ}

theorem ld_biHom_of_euler [CharZero k] {a b : ℕ} {g : MvPolynomial σ k}
    (hW : ∑ c, X (w c) * pderiv (w c) g = (a : k) • g)
    (hE : ∑ c, X (e c) * pderiv (e c) g = (b : k) • g) : BiHom w e a b g := by
  classical
  unfold BiHom
  intro m hm
  rw [MvPolynomial.mem_support_iff] at hm
  have hterm : ∀ i : σ, MvPolynomial.coeff m (X i * pderiv i g) = (m i : k) * MvPolynomial.coeff m g := by
    intro i
    rw [MvPolynomial.coeff_X_mul']
    split_ifs with hs
    · have hmi : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs)
      have e1 : m - Finsupp.single i 1 + Finsupp.single i 1 = m :=
        tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hmi)
      have e2 : (((m - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : k) + 1 = (m i : k) := by
        rw [Finsupp.tsub_apply, Finsupp.single_eq_same, ← Nat.cast_add_one, Nat.sub_add_cancel hmi]
      rw [MvPolynomial.coeff_pderiv, e1, e2, mul_comm]
    · simp at hs
      simp [hs]
  have key : ∀ (v : Fin r → σ) (n : ℕ), ∑ c, X (v c) * pderiv (v c) g = (n : k) • g → ∑ c, m (v c) = n := by
    intro v n hv
    have hcoef := congrArg (MvPolynomial.coeff m) hv
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul] at hcoef
    simp only [hterm] at hcoef
    rw [← Finset.sum_mul] at hcoef
    have hc := mul_right_cancel₀ hm hcoef
    exact_mod_cast hc
  exact ⟨key w a hW, key e b hE⟩

end

section fockSec
open Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {σ : Type}

end fockSec

section
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ}

end

section fockSec
open Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {σ : Type} {r : ℕ} {w e : Fin r → σ}

end fockSec

end Formalism.GM
