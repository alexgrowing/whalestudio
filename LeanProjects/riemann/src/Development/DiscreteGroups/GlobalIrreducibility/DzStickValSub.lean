import Development.DiscreteGroups.GlobalIrreducibility.DzStickValOne
import Development.DiscreteGroups.GlobalIrreducibility.DzStickDigits

noncomputable section

namespace DiscreteGroups.sglob.Stick

open IsDedekindDomain

namespace GSDatum

variable {p f : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Fintype k] [Algebra (ZMod p) k]
  {A : Type*} [CommRing A] [IsDedekindDomain A] {Q : HeightOneSpectrum A}
  (D : GSDatum p f k A Q)

theorem val_mul_le {χ₁ χ₂ : MulChar k A} (h : χ₁ * χ₂ ≠ 1) :
    Q.intValuation (gaussSum χ₁ D.ψ) * Q.intValuation (gaussSum χ₂ D.ψ) ≤
      Q.intValuation (gaussSum (χ₁ * χ₂) D.ψ) := by
  rw [← map_mul, ← jacobiSum_mul_nontrivial h D.ψ, map_mul]
  exact mul_le_of_le_one_right' (Q.intValuation_le_one _)

theorem gaussSum_pow_p (χ : MulChar k A) : gaussSum (χ ^ p) D.ψ = gaussSum χ D.ψ := by
  have : CharP k p := (Algebra.charP_iff (ZMod p) k p).1 inferInstance
  unfold gaussSum
  refine Fintype.sum_bijective (fun x : k => x ^ p) (frobeniusEquiv k p).bijective _ _ ?_
  intro x
  rw [MulChar.pow_apply' χ (Fact.out : p.Prime).ne_zero, map_pow]
  congr 1
  exact (psi_pow p k D.ζ D.prim.pow_eq_one x).symm

theorem ω_pow_add_inv (a b : ℕ) : (D.ω ^ (a + b))⁻¹ = (D.ω ^ a)⁻¹ * (D.ω ^ b)⁻¹ := by
  rw [pow_add, mul_inv]

theorem ω_pow_inv_ne_one {a : ℕ} (h0 : 0 < a) (ha : a < p ^ f - 1) : (D.ω ^ a)⁻¹ ≠ 1 := by
  rw [Ne, inv_eq_one]
  exact D.ω_pow_ne_one h0 ha

theorem pow_le_val_g_small {a : ℕ} (ha : a < p ^ f - 1) :
    Q.intValuation (D.ζ - 1) ^ a ≤ Q.intValuation (D.g a) := by
  induction a with
  | zero => rw [D.g_zero, pow_zero, Valuation.map_neg, map_one]
  | succ a ih =>
    have h1 : 1 < p ^ f - 1 := by omega
    have hne : (D.ω ^ a)⁻¹ * (D.ω ^ 1)⁻¹ ≠ 1 := by
      rw [← D.ω_pow_add_inv]
      exact D.ω_pow_inv_ne_one (Nat.succ_pos a) ha
    have h2 := D.val_mul_le hne
    rw [← D.ω_pow_add_inv] at h2
    have h3 : Q.intValuation (D.g a) * Q.intValuation (D.g 1) ≤ Q.intValuation (D.g (a + 1)) := h2
    rw [D.val_g_one h1] at h3
    rw [pow_succ]
    exact le_trans (mul_le_mul_left (ih (by omega)) _) h3

theorem pow_dsum_le_val_g {a : ℕ} (ha : a < p ^ f - 1) :
    Q.intValuation (D.ζ - 1) ^ dsum p a ≤ Q.intValuation (D.g a) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | h0
    · rw [dsum_of_lt hp (by omega)]
      exact D.pow_le_val_g_small ha
    · have hdiv : a / p < a := Nat.div_lt_self h0 hp
      have hmod : a % p ≤ a := Nat.mod_le a p
      have hdec : (D.ω ^ a)⁻¹ = (D.ω ^ (a % p))⁻¹ * ((D.ω ^ (a / p))⁻¹) ^ p := by
        rw [inv_pow, ← pow_mul, ← D.ω_pow_add_inv, mul_comm (a / p) p, Nat.mod_add_div]
      have hne : (D.ω ^ (a % p))⁻¹ * ((D.ω ^ (a / p))⁻¹) ^ p ≠ 1 := by
        rw [← hdec]
        exact D.ω_pow_inv_ne_one h0 ha
      have h2 := D.val_mul_le hne
      rw [← hdec, D.gaussSum_pow_p] at h2
      have h3 : Q.intValuation (D.g (a % p)) * Q.intValuation (D.g (a / p)) ≤
          Q.intValuation (D.g a) := h2
      rw [dsum_rec hp a, pow_add]
      exact le_trans (mul_le_mul' (D.pow_le_val_g_small (by omega)) (ih _ hdiv (by omega))) h3

theorem val_neg_one (χ : MulChar k A) : Q.intValuation (χ (-1)) = 1 := by
  have h : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; simp
  have h1 : Q.intValuation (χ (-1)) * Q.intValuation (χ (-1)) = 1 := by
    rw [← map_mul, h, map_one]
  refine le_antisymm (Q.intValuation_le_one _) ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Q.intValuation (χ (-1)) * Q.intValuation (χ (-1)) := h1.symm
    _ ≤ Q.intValuation (χ (-1)) := mul_le_of_le_one_right' (Q.intValuation_le_one _)

theorem val_g_mul_val_g_compl {a : ℕ} (h0 : 0 < a) (ha : a < p ^ f - 1) :
    Q.intValuation (D.g a) * Q.intValuation (D.g (p ^ f - 1 - a)) =
      Q.intValuation (D.ζ - 1) ^ (f * (p - 1)) := by
  have hprim : D.ψ.IsPrimitive := psi_isPrimitive p k D.ζ D.prim
  have hne := D.ω_pow_inv_ne_one h0 ha
  have hinv : (D.ω ^ (p ^ f - 1 - a))⁻¹ = ((D.ω ^ a)⁻¹)⁻¹ := by
    rw [inv_inv, inv_eq_iff_mul_eq_one, ← pow_add, Nat.sub_add_cancel ha.le, D.ω_pow_card]
  have hcard := gaussSum_mul_gaussSum_eq_card hne hprim
  have hshift := gaussSum_mulShift ((D.ω ^ a)⁻¹)⁻¹ D.ψ (-1 : kˣ)
  have hψ : AddChar.mulShift D.ψ ((-1 : kˣ) : k) = D.ψ⁻¹ := by
    rw [AddChar.inv_mulShift]; simp
  rw [hψ] at hshift
  have hv : Q.intValuation (gaussSum ((D.ω ^ a)⁻¹)⁻¹ D.ψ⁻¹) =
      Q.intValuation (gaussSum ((D.ω ^ a)⁻¹)⁻¹ D.ψ) := by
    rw [← hshift, map_mul]
    have : (((-1 : kˣ) : k)) = -1 := by simp
    rw [this, val_neg_one, one_mul]
  unfold g
  rw [hinv, ← hv, ← map_mul, hcard, D.card_eq, Nat.cast_pow, map_pow, D.val_p, ← pow_mul,
    mul_comm f]

end GSDatum

end DiscreteGroups.sglob.Stick
