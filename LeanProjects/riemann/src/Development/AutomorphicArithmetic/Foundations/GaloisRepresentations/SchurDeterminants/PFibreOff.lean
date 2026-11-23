import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

open Finset MvPolynomial UpperTheory.Gal.Schur

private lemma prod_scale_at {R : Type} [CommRing R] {n : ℕ} (y : R) (i : Fin n) (g : Fin n → R) :
    ∏ k, scaleAt y i g k = y * ∏ k, g k := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ i), ← Finset.mul_prod_erase univ g (mem_univ i)]
  have h1 : scaleAt y i g i = y * g i := by simp [scaleAt]
  have h2 : ∏ k ∈ univ.erase i, scaleAt y i g k = ∏ k ∈ univ.erase i, g k :=
    Finset.prod_congr rfl (fun k hk => by simp [scaleAt, ne_of_mem_erase hk])
  rw [h1, h2]; ring

theorem UpperTheory.Gal.Schur.fibreOff_of :
    SchurYOff → SchurHomog → SchurDet → FibreOff := by
  intro hY hH hD
  intro R ι _ _ _ _ n t₀ t₁ h ε lam m hm g y hu
  have hsplit : ∀ F : ι → R,
      ∏ t, F t = F t₀ * (F t₁ * ∏ t ∈ (univ.erase t₀).erase t₁, F t) := by
    intro F
    rw [← Finset.mul_prod_erase univ F (mem_univ t₀),
      ← Finset.mul_prod_erase (univ.erase t₀) F (mem_erase.2 ⟨h.symm, mem_univ _⟩)]
  have hlam : lam t₀ = fun i => (fun _ => 0 : Fin n → ℕ) i + m := by
    funext i; simp [hm]
  have hsch0 : ∀ h' : Fin n → R, sch (lam t₀) h' = (∏ k, h' k) ^ m := by
    intro h'
    rw [hlam]
    exact ((hD R n h').2 _ m).trans (by rw [(hD R n h').1, mul_one])
  have hrest : ∀ i, ∏ t ∈ (univ.erase t₀).erase t₁, sch (lam t) (twist t₀ t₁ ε y i g t) =
      y ^ (∑ t ∈ (univ.erase t₀).erase t₁, ε t * ∑ i, lam t i) *
        ∏ t ∈ (univ.erase t₀).erase t₁, sch (lam t) (g t) := by
    intro i
    have hc : ∀ t ∈ (univ.erase t₀).erase t₁, sch (lam t) (twist t₀ t₁ ε y i g t) =
        y ^ (ε t * ∑ i, lam t i) * sch (lam t) (g t) := by
      intro t ht
      have ht1 : t ≠ t₁ := ne_of_mem_erase ht
      have ht0 : t ≠ t₀ := ne_of_mem_erase (mem_of_mem_erase ht)
      simp only [twist, if_neg ht0, if_neg ht1]
      rw [hH, ← pow_mul]
    rw [Finset.prod_congr rfl hc, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have tw0 : ∀ i, twist t₀ t₁ ε y i g t₀ = scaleAt y i (g t₀) := by
    intro i; simp [twist]
  have tw1 : ∀ i, twist t₀ t₁ ε y i g t₁ = scaleOff y i (g t₁) := by
    intro i; simp [twist, h.symm]
  have hterm : ∀ i : Fin n,
      (∏ t, sch (lam t) (twist t₀ t₁ ε y i g t)) *
          ∏ k ∈ univ.erase i, ((g t₁ i - y * g t₁ k) * Ring.inverse (g t₁ i - g t₁ k)) =
        (y ^ m * (∏ k, g t₀ k) ^ m *
            (y ^ (∑ t ∈ (univ.erase t₀).erase t₁, ε t * ∑ i, lam t i) *
              ∏ t ∈ (univ.erase t₀).erase t₁, sch (lam t) (g t))) *
          (sch (lam t₁) (scaleOff y i (g t₁)) *
            ∏ k ∈ univ.erase i, ((g t₁ i - y * g t₁ k) * Ring.inverse (g t₁ i - g t₁ k))) := by
    intro i
    rw [hsplit (fun t => sch (lam t) (twist t₀ t₁ ε y i g t)), tw0, tw1, hrest, hsch0,
      prod_scale_at, mul_pow]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum, hY R n (lam t₁) (g t₁) y hu,
    hsplit (fun t => sch (lam t) (g t)), hsch0, pow_add]
  ring
