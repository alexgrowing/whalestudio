import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CliffordCoeff

section SlopeTestRemainingChoices

variable {R : Type} [Ring R]

theorem comm_prod (D C X : R) :
    (D * C) * X - X * (D * C) = D * (C * X + X * C) - (D * X + X * D) * C := by
  noncomm_ring

theorem ad_mul (A x y : R) :
    A * (x * y) - (x * y) * A = (A * x - x * A) * y + x * (A * y - y * A) := by
  noncomm_ring

theorem ad_sub (x y z : R) :
    (x - y) * z - z * (x - y) = (x * z - z * x) - (y * z - z * y) := by
  noncomm_ring

theorem comm_sum {ι : Type} [Fintype ι] (u v : ι → R) (x : R) :
    (∑ r, u r * v r) * x - x * (∑ r, u r * v r)
      = ∑ r, (u r * (v r * x + x * v r) - (u r * x + x * u r) * v r) := by
  simp only [sum_mul, mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun r _ => comm_prod _ _ _

variable {n : ℕ} {τ : Fin n → Fin n → Prop} [DecidableRel τ] {c d L : Fin n → Fin n → R}
  {p q : Fin n}

theorem ad_d
    (hd : ∀ a b a' b', d a b * d a' b' + d a' b' * d a b = 0)
    (hcd : ∀ a b a' b', c a b * d a' b' + d a' b' * c a b = if a = a' ∧ b = b' ∧ τ a b then 1 else 0)
    (hdτ : ∀ a b, ¬τ a b → d a b = 0)
    (h1 : ∀ b, τ p b ↔ τ q b) (h2 : ∀ a, τ a p ↔ τ a q) (a e : Fin n) :
    (∑ r, d p r * c q r - ∑ r, d r q * c r p) * d a e
        - d a e * (∑ r, d p r * c q r - ∑ r, d r q * c r p)
      = (if q = a then d p e else 0) - (if p = e then d a q else 0) := by
  have e1 : (∑ r, d p r * c q r) * d a e - d a e * (∑ r, d p r * c q r)
      = if q = a then d p e else 0 := by
    rw [comm_sum]
    simp only [hd, hcd, zero_mul, sub_zero]
    rw [Fintype.sum_eq_single e (fun r hr => by simp [hr])]
    by_cases hq : q = a
    · subst hq
      by_cases ht : τ q e
      · simp [ht]
      · have : d p e = 0 := hdτ _ _ fun h => ht ((h1 e).1 h)
        simp [ht, this]
    · simp [hq]
  have e2 : (∑ r, d r q * c r p) * d a e - d a e * (∑ r, d r q * c r p)
      = if p = e then d a q else 0 := by
    rw [comm_sum]
    simp only [hd, hcd, zero_mul, sub_zero]
    rw [Fintype.sum_eq_single a (fun r hr => by simp [hr])]
    by_cases hp : p = e
    · subst hp
      by_cases ht : τ a p
      · simp [ht]
      · have : d a q = 0 := hdτ _ _ fun h => ht ((h2 a).2 h)
        simp [ht, this]
    · simp [hp]
  rw [ad_sub, e1, e2]

theorem ad_c
    (hc : ∀ a b a' b', c a b * c a' b' + c a' b' * c a b = 0)
    (hcd : ∀ a b a' b', c a b * d a' b' + d a' b' * c a b = if a = a' ∧ b = b' ∧ τ a b then 1 else 0)
    (hcτ : ∀ a b, ¬τ a b → c a b = 0)
    (h1 : ∀ b, τ p b ↔ τ q b) (h2 : ∀ a, τ a p ↔ τ a q) (a b : Fin n) :
    (∑ r, d p r * c q r - ∑ r, d r q * c r p) * c a b
        - c a b * (∑ r, d p r * c q r - ∑ r, d r q * c r p)
      = (if q = b then c a p else 0) - (if p = a then c q b else 0) := by
  have hdc : ∀ a b a' b', d a' b' * c a b + c a b * d a' b'
      = if a = a' ∧ b = b' ∧ τ a b then 1 else 0 := fun a b a' b' => by
    rw [add_comm]; exact hcd a b a' b'
  have e1 : (∑ r, d p r * c q r) * c a b - c a b * (∑ r, d p r * c q r)
      = - (if p = a then c q b else 0) := by
    rw [comm_sum]
    simp only [hc, hdc, mul_zero, zero_sub, sum_neg_distrib]
    rw [Fintype.sum_eq_single b (fun r hr => by simp [hr.symm])]
    by_cases hp : p = a
    · subst hp
      by_cases ht : τ p b
      · simp [ht]
      · have : c q b = 0 := hcτ _ _ fun h => ht ((h1 b).2 h)
        simp [ht, this]
    · simp [hp, Ne.symm hp]
  have e2 : (∑ r, d r q * c r p) * c a b - c a b * (∑ r, d r q * c r p)
      = - (if q = b then c a p else 0) := by
    rw [comm_sum]
    simp only [hc, hdc, mul_zero, zero_sub, sum_neg_distrib]
    rw [Fintype.sum_eq_single a (fun r hr => by simp [hr.symm])]
    by_cases hq : q = b
    · subst hq
      by_cases ht : τ a q
      · simp [ht]
      · have : c a p = 0 := hcτ _ _ fun h => ht ((h2 a).1 h)
        simp [ht, this]
    · simp [hq, Ne.symm hq]
  rw [ad_sub, e1, e2]
  abel

theorem ad_triple (A : R)
    (hAd : ∀ a e, A * d a e - d a e * A
      = (if q = a then d p e else 0) - (if p = e then d a q else 0))
    (hAc : ∀ a b, A * c a b - c a b * A
      = (if q = b then c a p else 0) - (if p = a then c q b else 0)) :
    A * (∑ a, ∑ b, ∑ e, d a e * c b e * c a b) - (∑ a, ∑ b, ∑ e, d a e * c b e * c a b) * A
      = 0 := by
  have step : ∀ a b e, A * (d a e * c b e * c a b) - (d a e * c b e * c a b) * A
      = (if q = a then d p e else 0) * c b e * c a b
        - (if p = e then d a q else 0) * c b e * c a b
        + d a e * (if q = e then c b p else 0) * c a b
        - d a e * (if p = b then c q e else 0) * c a b
        + d a e * c b e * (if q = b then c a p else 0)
        - d a e * c b e * (if p = a then c q b else 0) := by
    intro a b e
    rw [ad_mul, ad_mul, hAd, hAc, hAc]
    simp only [sub_mul, mul_sub, add_mul, mul_add, mul_assoc]
    abel
  have s1 : ∑ a, ∑ b, ∑ e, (if q = a then d p e else 0) * c b e * c a b
      = ∑ b, ∑ e, d p e * c b e * c q b := by
    rw [Fintype.sum_eq_single q (fun a ha => by simp [Ne.symm ha])]
    simp
  have s6 : ∑ a, ∑ b, ∑ e, d a e * c b e * (if p = a then c q b else 0)
      = ∑ b, ∑ e, d p e * c b e * c q b := by
    rw [Fintype.sum_eq_single p (fun a ha => by simp [Ne.symm ha])]
    simp
  have s2 : ∑ a, ∑ b, ∑ e, (if p = e then d a q else 0) * c b e * c a b
      = ∑ a, ∑ b, d a q * c b p * c a b := by
    simp only [ite_mul, zero_mul, sum_ite_eq, mem_univ, if_true]
  have s3 : ∑ a, ∑ b, ∑ e, d a e * (if q = e then c b p else 0) * c a b
      = ∑ a, ∑ b, d a q * c b p * c a b := by
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, sum_ite_eq, mem_univ, if_true]
  have s4 : ∑ a, ∑ b, ∑ e, d a e * (if p = b then c q e else 0) * c a b
      = ∑ a, ∑ e, d a e * c q e * c a p := by
    refine sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_eq_single p (fun b hb => by simp [Ne.symm hb])]
    simp
  have s5 : ∑ a, ∑ b, ∑ e, d a e * c b e * (if q = b then c a p else 0)
      = ∑ a, ∑ e, d a e * c q e * c a p := by
    refine sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_eq_single q (fun b hb => by simp [Ne.symm hb])]
    simp
  have hs : A * (∑ a, ∑ b, ∑ e, d a e * c b e * c a b)
      - (∑ a, ∑ b, ∑ e, d a e * c b e * c a b) * A
      = ∑ a, ∑ b, ∑ e, (A * (d a e * c b e * c a b) - (d a e * c b e * c a b) * A) := by
    simp only [mul_sum, sum_mul, sum_sub_distrib]
  rw [hs]
  simp only [step, sum_add_distrib, sum_sub_distrib]
  rw [s1, s2, s3, s4, s5, s6]
  abel

theorem ad_first (A : R) (hAL : ∀ a b, A * L a b = L a b * A)
    (hAc : ∀ a b, A * c a b - c a b * A
      = (if q = b then c a p else 0) - (if p = a then c q b else 0)) :
    A * (∑ a, ∑ b, L a b * c a b) - (∑ a, ∑ b, L a b * c a b) * A
      = ∑ a, L a q * c a p - ∑ b, L p b * c q b := by
  have hs : A * (∑ a, ∑ b, L a b * c a b) - (∑ a, ∑ b, L a b * c a b) * A
      = ∑ a, ∑ b, (A * (L a b * c a b) - (L a b * c a b) * A) := by
    simp only [mul_sum, sum_mul, sum_sub_distrib]
  have step : ∀ a b, A * (L a b * c a b) - (L a b * c a b) * A
      = L a b * (if q = b then c a p else 0) - L a b * (if p = a then c q b else 0) := by
    intro a b
    rw [ad_mul, hAL, sub_self, zero_mul, zero_add, hAc, mul_sub]
  rw [hs]
  simp only [step, sum_sub_distrib]
  congr 1
  · simp only [mul_ite, mul_zero, sum_ite_eq, mem_univ, if_true]
  · rw [Fintype.sum_eq_single p (fun a ha => by simp [Ne.symm ha])]
    simp

theorem ad_L_first
    (hLc : ∀ a b a' b', Commute (L a b) (c a' b'))
    (hLL : ∀ a b, L p q * L a b - L a b * L p q
      = (if q = a then L p b else 0) - (if b = p then L a q else 0)) :
    L p q * (∑ a, ∑ b, L a b * c a b) - (∑ a, ∑ b, L a b * c a b) * L p q
      = ∑ b, L p b * c q b - ∑ a, L a q * c a p := by
  have hs : L p q * (∑ a, ∑ b, L a b * c a b) - (∑ a, ∑ b, L a b * c a b) * L p q
      = ∑ a, ∑ b, (L p q * (L a b * c a b) - (L a b * c a b) * L p q) := by
    simp only [mul_sum, sum_mul, sum_sub_distrib]
  have step : ∀ a b, L p q * (L a b * c a b) - (L a b * c a b) * L p q
      = (if q = a then L p b else 0) * c a b - (if b = p then L a q else 0) * c a b := by
    intro a b
    rw [ad_mul, hLL, (hLc p q a b).eq, sub_self, mul_zero, add_zero, sub_mul]
  rw [hs]
  simp only [step, sum_sub_distrib]
  congr 1
  · rw [Fintype.sum_eq_single q (fun a ha => by simp [Ne.symm ha])]
    simp
  · simp only [ite_mul, zero_mul, sum_ite_eq', mem_univ, if_true]

end SlopeTestRemainingChoices

theorem commute_shifted_dirac : ∀ (n : ℕ) (R : Type) [Ring R] (τ : Fin n → Fin n → Prop) [DecidableRel τ] (c d L : Fin n → Fin n → R) (p q : Fin n),
    (∀ a b a' b', c a b * c a' b' + c a' b' * c a b = 0) →
    (∀ a b a' b', d a b * d a' b' + d a' b' * d a b = 0) →
    (∀ a b a' b', c a b * d a' b' + d a' b' * c a b = if a = a' ∧ b = b' ∧ τ a b then 1 else 0) →
    (∀ a b, ¬τ a b → c a b = 0) → (∀ a b, ¬τ a b → d a b = 0) →
    (∀ b, τ p b ↔ τ q b) → (∀ a, τ a p ↔ τ a q) →
    (∀ a b a' b', Commute (L a b) (c a' b')) → (∀ a b a' b', Commute (L a b) (d a' b')) →
    (∀ a b, L p q * L a b - L a b * L p q = (if q = a then L p b else 0) - (if b = p then L a q else 0)) →
    Commute (L p q + (∑ r, d p r * c q r - ∑ r, d r q * c r p))
      ((∑ a, ∑ b, L a b * c a b) + ∑ a, ∑ b, ∑ e, d a e * c b e * c a b) := by
  intro n R _ τ _ c d L p q hc hd hcd hcτ hdτ h1 h2 hLc hLd hLL
  have hAd := ad_d (p := p) (q := q) (c := c) hd hcd hdτ h1 h2
  have hAc := ad_c (p := p) (q := q) (d := d) hc hcd hcτ h1 h2
  have hAL : ∀ a b, (∑ r, d p r * c q r - ∑ r, d r q * c r p) * L a b
      = L a b * (∑ r, d p r * c q r - ∑ r, d r q * c r p) := by
    intro a b
    have : Commute (∑ r, d p r * c q r - ∑ r, d r q * c r p) (L a b) :=
      Commute.sub_left
        (Commute.sum_left _ _ _ fun r _ => ((hLd a b p r).symm).mul_left (hLc a b q r).symm)
        (Commute.sum_left _ _ _ fun r _ => ((hLd a b r q).symm).mul_left (hLc a b r p).symm)
    exact this.eq
  have hB1 := ad_first (L := L) (p := p) (q := q) (c := c) _ hAL hAc
  have hB2 := ad_L_first (L := L) (p := p) (q := q) (c := c) hLc hLL
  have hQ1 := ad_triple (p := p) (q := q) (c := c) (d := d) _ hAd hAc
  have hQ2 : Commute (L p q) (∑ a, ∑ b, ∑ e, d a e * c b e * c a b) :=
    Commute.sum_right _ _ _ fun a _ => Commute.sum_right _ _ _ fun b _ =>
      Commute.sum_right _ _ _ fun e _ =>
        ((hLd p q a e).mul_right (hLc p q b e)).mul_right (hLc p q a b)
  generalize (∑ r, d p r * c q r - ∑ r, d r q * c r p) = A at *
  generalize (∑ a, ∑ b, ∑ e, d a e * c b e * c a b) = Q at *
  generalize (∑ a, ∑ b, L a b * c a b) = B at *
  have key : (L p q + A) * (B + Q) - (B + Q) * (L p q + A)
      = (L p q * B - B * L p q) + (A * B - B * A) + (L p q * Q - Q * L p q) + (A * Q - Q * A) := by
    noncomm_ring
  have hQ2' : L p q * Q - Q * L p q = 0 := sub_eq_zero.2 hQ2.eq
  rw [hB1, hB2, hQ1, hQ2'] at key
  refine sub_eq_zero.1 ?_
  rw [key]
  abel

end GlobalTheory.CompanionTheory.CliffordCoeff
