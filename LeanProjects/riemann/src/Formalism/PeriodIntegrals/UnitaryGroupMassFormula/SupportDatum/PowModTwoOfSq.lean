import Mathlib
import Formalism.PeriodIntegrals.SupportParts

noncomputable section

namespace PI.SupportDatumW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem twist_mul {D : Formalism.BasicNotions.D7} (p : PlF D) (s : ℕ) (x : (D.s.atP p).Ep) :
    twist p s x = x * twist p s 1 := by
  unfold twist
  rcases (D.s.atP p).split with _ | sg
  · simp
  · apply sg.e.injective
    ext <;> simp [mul_comm]

theorem twist_one_pow {D : Formalism.BasicNotions.D7} (p : PlF D) (s : ℕ) :
    twist p s (1 : (D.s.atP p).Ep) = twist p 1 (1 : (D.s.atP p).Ep) ^ s := by
  unfold twist
  rcases (D.s.atP p).split with _ | sg
  · simp
  · apply sg.e.injective
    ext <;> simp

theorem twist_sq {D : Formalism.BasicNotions.D7} (p : PlF D) :
    twist p 1 (1 : (D.s.atP p).Ep) ^ 2 = 1 := by
  unfold twist
  rcases (D.s.atP p).split with _ | sg
  · simp
  · apply sg.e.injective
    ext <;> simp

theorem pow_mod_two_of_sq {A : Type} [Monoid A] (τ : A) (h : τ ^ 2 = 1) (n : ℕ) : τ ^ n = τ ^ (n % 2) := by
  conv_lhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul, h, one_pow, one_mul]

def hF (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) (a s : ℕ) : (D.s.atP p).Ep :=
  Ring.inverse ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^
    (nu D.R.rS a (a + s - 1))) * twist p s 1 * Ring.inverse (qE p)

def gF (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (a s : ℕ) (t : D.host.E) :
    (D.s.atP p).Ep :=
  if a + s - 1 = D.R.rS + 1 ∧ s = 1 then Ring.inverse ((D.s.atP p).ιE t) * blkTop δ T T' p a s t
  else hF D δ p a s

theorem blkTop_eq (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (a s : ℕ)
    (t : D.host.E) (ht : t ≠ 0) :
    blkTop δ T T' p a s t = (D.s.atP p).ιE t * gF D δ T T' p a s t := by
  unfold gF
  by_cases h : a + s - 1 = D.R.rS + 1 ∧ s = 1
  · rw [if_pos h, ← mul_assoc, Ring.mul_inverse_cancel _ ((isUnit_iff_ne_zero.mpr ht).map _), one_mul]
  · rw [if_neg h]
    simp only [blkTop, blkMod, tMod, hF, if_neg h, sub_zero]
    rw [twist_mul p s ((D.s.atP p).ιE t)]
    ring

def prodFac {A B : Type} [CommMonoid B] (g : ℕ → ℕ → A → B) : ℕ → List (A × ℕ) → B
  | _, [] => 1
  | a, (t, s) :: rest => g a s t ^ s * prodFac g (a + s) rest

theorem prodFac_append {A B : Type} [CommMonoid B] (g : ℕ → ℕ → A → B) (l1 l2 : List (A × ℕ)) (a : ℕ) :
    prodFac g a (l1 ++ l2) = prodFac g a l1 * prodFac g (a + (l1.map Prod.snd).sum) l2 := by
  induction l1 generalizing a with
  | nil => simp [prodFac]
  | cons x l ih =>
    obtain ⟨t, s⟩ := x
    simp [prodFac, ih, mul_assoc, add_assoc]

def Hm (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) (a m : ℕ) : (D.s.atP p).Ep :=
  ∏ k ∈ Finset.range m, hF D δ p (a + k) 1

theorem Hm_add (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) (a m m' : ℕ) :
    Hm D δ p a (m + m') = Hm D δ p a m * Hm D δ p (a + m) m' := by
  unfold Hm
  rw [Finset.prod_range_add]
  simp only [add_assoc]

theorem sum_nu (r a s : ℕ) (ha : 1 ≤ a) (hs : a + s ≤ r + 2) :
    ∑ k ∈ Finset.range s, nu r (a + k) (a + k + 1 - 1) = nu r a (a + s - 1) * s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    obtain ⟨f, hf⟩ : ∃ f, 2 * (r + 1) - a - (a + s) = s + f :=
      ⟨2 * (r + 1) - a - (a + s) - s, by omega⟩
    have h1 : a + s + 1 - 1 = a + s := by omega
    have h2 : a + (s + 1) - 1 = a + s := by omega
    have e1 : 2 * (r + 1) - a - (a + s - 1) = s + f + 1 := by omega
    have e2 : 2 * (r + 1) - (a + s) - (a + s) = f := by omega
    unfold nu
    rw [h1, h2, e1, e2, hf]
    ring

theorem hF_pow (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) (a s : ℕ) (ha : 1 ≤ a)
    (hs : a + s ≤ D.R.rS + 2) : hF D δ p a s ^ s = Hm D δ p a s := by
  have hsum := sum_nu D.R.rS a s ha hs
  have hmod : s * s % 2 = s % 2 := by
    rw [Nat.mul_mod]
    rcases Nat.mod_two_eq_zero_or_one s with h | h <;> rw [h]
  unfold Hm hF
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
    Finset.card_range, mul_pow, mul_pow]
  congr 1
  congr 1
  · simp only [← Ring.inverse_pow, ← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum, hsum]
  · rw [twist_one_pow p s, ← pow_mul, pow_mod_two_of_sq _ (twist_sq p) (s * s), hmod,
      ← pow_mod_two_of_sq _ (twist_sq p) s]

theorem prodFac_noTop (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D)
    (bs : List (D.host.E × ℕ)) (a : ℕ) (ha : 1 ≤ a) (hsz : ∀ b ∈ bs, 1 ≤ b.2)
    (hend : a + (bs.map Prod.snd).sum ≤ D.R.rS + 1) :
    prodFac (gF D δ T T' p) a bs = Hm D δ p a (bs.map Prod.snd).sum := by
  induction bs generalizing a with
  | nil => simp [prodFac, Hm]
  | cons b rest ih =>
    obtain ⟨t, s⟩ := b
    have hs1 : 1 ≤ s := hsz (t, s) (by simp)
    have hrest : ∀ b ∈ rest, 1 ≤ b.2 := fun b hb => hsz b (by simp [hb])
    simp only [List.map_cons, List.sum_cons] at hend ⊢
    have hnt : ¬ (a + s - 1 = D.R.rS + 1 ∧ s = 1) := by omega
    rw [prodFac, gF, if_neg hnt, hF_pow D δ p a s ha (by omega),
      ih (a + s) (by omega) hrest (by omega), ← Hm_add]

end PI.SupportDatumW
