import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private lemma prod_scaleOff {R : Type} [CommRing R] {n : ℕ} (y : R) (i : Fin n) (g : Fin n → R) :
    ∏ k, scaleOff y i g k = y ^ (n - 1) * ∏ k, g k := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ i), ← Finset.mul_prod_erase univ g (mem_univ i)]
  have h : ∏ k ∈ univ.erase i, scaleOff y i g k = ∏ k ∈ univ.erase i, (y * g k) :=
    Finset.prod_congr rfl (fun k hk => by simp [scaleOff, (mem_erase.1 hk).1])
  rw [h, prod_mul_distrib, prod_const, card_erase_of_mem (mem_univ i), card_univ,
    Fintype.card_fin]
  simp only [scaleOff, if_true]
  ring

theorem fibre_of : SchurY → SchurHomog → SchurDet → Fibre := by
  intro hY hH hD R ι _ _ _ _ n t₀ t₁ h01 ε lam m hm g y hu
  have hconst : ∀ h : Fin n → R, sch (lam t₁) h = (∏ k, h k) ^ m := by
    intro h
    have e := (hD R n h).2 (fun _ => 0) m
    simp only [zero_add, (hD R n h).1, mul_one] at e
    have hl : lam t₁ = fun _ => m := funext hm
    rw [hl, e]
  have h10 : t₁ ≠ t₀ := fun h => h01 h.symm
  have h1mem : t₁ ∈ univ.erase t₀ := mem_erase.mpr ⟨h10, mem_univ _⟩
  have hrest : ∀ i, ∏ t ∈ (univ.erase t₀).erase t₁, sch (lam t) (twist t₀ t₁ ε y i g t) =
      y ^ (∑ t ∈ (univ.erase t₀).erase t₁, ε t * ∑ k, lam t k) *
        ∏ t ∈ (univ.erase t₀).erase t₁, sch (lam t) (g t) := by
    intro i
    rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    apply prod_congr rfl
    intro t ht
    have ht1 : t ≠ t₁ := (mem_erase.mp ht).1
    have ht0 : t ≠ t₀ := (mem_erase.mp (mem_erase.mp ht).2).1
    simp only [twist, if_neg ht0, if_neg ht1]
    rw [hH R n (lam t) (g t) (y ^ ε t), ← pow_mul]
  have hi : ∀ i, ∏ t, sch (lam t) (twist t₀ t₁ ε y i g t) =
      sch (lam t₀) (scaleAt y i (g t₀)) *
        (y ^ ((n - 1) * m + ∑ t ∈ (univ.erase t₀).erase t₁, ε t * ∑ k, lam t k) *
          ∏ t ∈ univ.erase t₀, sch (lam t) (g t)) := by
    intro i
    rw [← mul_prod_erase univ _ (mem_univ t₀), ← mul_prod_erase (univ.erase t₀) _ h1mem,
      ← mul_prod_erase (univ.erase t₀) (fun t => sch (lam t) (g t)) h1mem, hrest i]
    simp only [twist, eq_self_iff_true, ↓reduceIte, h10]
    rw [hconst, hconst, prod_scaleOff, mul_pow, ← pow_mul, pow_add]
    ring
  calc ∑ i, (∏ t, sch (lam t) (twist t₀ t₁ ε y i g t)) *
        ∏ k ∈ univ.erase i, (g t₀ k - y * g t₀ i) * Ring.inverse (g t₀ k - g t₀ i)
      = (y ^ ((n - 1) * m + ∑ t ∈ (univ.erase t₀).erase t₁, ε t * ∑ k, lam t k) *
          ∏ t ∈ univ.erase t₀, sch (lam t) (g t)) *
        ∑ i, sch (lam t₀) (scaleAt y i (g t₀)) *
          ∏ k ∈ univ.erase i, (g t₀ k - y * g t₀ i) * Ring.inverse (g t₀ k - g t₀ i) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        rw [hi i]
        ring
    _ = _ := by
        rw [hY R n (lam t₀) (g t₀) y hu, ← mul_prod_erase univ (fun t => sch (lam t) (g t)) (mem_univ t₀)]
        ring

end UpperTheory.Gal.Schur
