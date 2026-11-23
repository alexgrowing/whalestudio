import Formalism.DegreeFormula.FlagDegFormula
import Formalism.DegreeFormula.PointDegree.PermExpInj

open MvPolynomial

namespace Formalism.DegreeFormula.PPowSum
open Formalism.DegreeFormula

theorem degFl_add {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (P Q : MvPolynomial (ι × Fin N) ℝ) :
    degFl ι N (P + Q) = degFl ι N P + degFl ι N Q := by
  simp only [degFl, coeff_add, mul_add, Finset.sum_add_distrib]

theorem degFl_C_mul {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (c : ℝ) (P : MvPolynomial (ι × Fin N) ℝ) :
    degFl ι N (C c * P) = c * degFl ι N P := by
  simp only [degFl, coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem degFl_zero {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} :
    degFl ι N (0 : MvPolynomial (ι × Fin N) ℝ) = 0 := by
  simp [degFl]

theorem degFl_sum {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} {α : Type*} (s : Finset α)
    (f : α → MvPolynomial (ι × Fin N) ℝ) :
    degFl ι N (∑ a ∈ s, f a) = ∑ a ∈ s, degFl ι N (f a) := by
  classical
  refine Finset.induction_on s (by simp [degFl_zero]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, degFl_add, ih]

theorem permExp_apply {ι : Type} [Fintype ι] {N : ℕ} (σ : ι → Equiv.Perm (Fin N)) (x : ι × Fin N) :
    permExp σ x = N - 1 - ((σ x.1 x.2 : Fin N) : ℕ) := by
  rfl

theorem degree_permExp {ι : Type} [Fintype ι] {N : ℕ} (σ : ι → Equiv.Perm (Fin N)) :
    (permExp σ).degree = dimFl ι N := by
  rw [Finsupp.degree_eq_sum]
  simp only [permExp_apply]
  rw [Fintype.sum_prod_type]
  have h : ∀ t : ι, ∑ i : Fin N, (N - 1 - ((σ t i : Fin N) : ℕ)) = N * (N - 1) / 2 := by
    intro t
    rw [Equiv.sum_comp (σ t) (fun j : Fin N => N - 1 - (j : ℕ)),
      Fin.sum_univ_eq_sum_range (fun j => N - 1 - j) N, Finset.sum_range_reflect (fun j => j) N,
      Finset.sum_range_id]
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul, dimFl]

theorem degFlHomog : DegFlHomog := by
  intro ι _ _ N d P hP hd
  unfold degFl
  rw [Finset.sum_eq_zero, mul_zero]
  intro σ _
  rw [hP.coeff_eq_zero, mul_zero]
  rw [degree_permExp]
  exact Ne.symm hd

theorem coeff_Xpow_mul {ι : Type} [Fintype ι] {N : ℕ} (x : ι × Fin N) (k : ℕ)
    (m : (ι × Fin N) →₀ ℕ) (P : MvPolynomial (ι × Fin N) ℝ) :
    (X x ^ k * P).coeff m = if k ≤ m x then P.coeff (m - Finsupp.single x k) else 0 := by
  rw [X_pow_eq_monomial, coeff_monomial_mul', one_mul]
  by_cases h : k ≤ m x
  · rw [if_pos (Finsupp.single_le_iff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (Finsupp.single_le_iff.mp h')), if_neg h]

def sgnP {ι : Type} [Fintype ι] {N : ℕ} (σ : ι → Equiv.Perm (Fin N)) : ℝ :=
  ∏ t, ((Equiv.Perm.sign (σ t) : ℤ) : ℝ)

theorem permSign_mulSingle_swap_mul {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (τ : ι) (a b : Fin N)
    (hab : a ≠ b) (σ : ι → Equiv.Perm (Fin N)) :
    sgnP (Pi.mulSingle τ (Equiv.swap a b) * σ) = -sgnP σ := by
  unfold sgnP
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  have h1 : ∏ t ∈ Finset.univ.erase τ,
      ((Equiv.Perm.sign ((Pi.mulSingle τ (Equiv.swap a b) * σ : ι → Equiv.Perm (Fin N)) t) : ℤ) : ℝ) =
      ∏ t ∈ Finset.univ.erase τ, ((Equiv.Perm.sign (σ t) : ℤ) : ℝ) := by
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase ht), one_mul]
  rw [h1, Pi.mul_apply, Pi.mulSingle_eq_same, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
  simp only [Units.val_mul, Units.val_neg, Units.val_one, Int.cast_mul, Int.cast_neg, Int.cast_one]
  ring

theorem mulSingle_mul_apply {ι : Type} [DecidableEq ι] {N : ℕ} (τ : ι) (s : Equiv.Perm (Fin N))
    (σ : ι → Equiv.Perm (Fin N)) (t : ι) (i : Fin N) :
    ((Pi.mulSingle τ s * σ : ι → Equiv.Perm (Fin N)) t) i = if t = τ then s (σ τ i) else σ t i := by
  rw [Pi.mul_apply]
  split_ifs with h
  · subst h
    rw [Pi.mulSingle_eq_same, Equiv.Perm.mul_apply]
  · rw [Pi.mulSingle_eq_of_ne h, one_mul]

theorem rem_eq {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (σ : ι → Equiv.Perm (Fin N)) (τ : ι)
    (k : ℕ) (j j' : Fin N) (hj : (j' : ℕ) = j + k) (hne : j ≠ j') :
    permExp (Pi.mulSingle τ (Equiv.swap j j') * σ) - Finsupp.single (τ, (σ τ).symm j') k =
      permExp σ - Finsupp.single (τ, (σ τ).symm j) k := by
  have hne' : (j : ℕ) ≠ j' := fun h => hne (Fin.ext h)
  ext ⟨t, i⟩
  simp only [Finsupp.coe_tsub, Pi.sub_apply, permExp_apply, mulSingle_mul_apply, Finsupp.single_apply,
    Prod.mk.injEq, Equiv.symm_apply_eq, Equiv.swap_apply_def]
  by_cases ht : t = τ
  · subst ht
    by_cases h1 : σ t i = j
    · simp [h1, hne, Ne.symm hne] <;> omega
    · by_cases h2 : σ t i = j'
      · simp [h2, hne, Ne.symm hne] <;> omega
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · simp [ht, Ne.symm ht]

theorem sum_eq_zero_of_anti {G : Type*} [Group G] [Fintype G] (ρ : G) (F : G → ℝ)
    (h : ∀ g, F (ρ * g) = -F g) : ∑ g, F g = 0 := by
  have h1 : ∑ g, F (ρ * g) = ∑ g, F g := Fintype.sum_equiv (Equiv.mulLeft ρ) _ _ (fun _ => rfl)
  simp only [h, Finset.sum_neg_distrib] at h1
  linarith

theorem slice {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (τ : ι) (k : ℕ) (hk : 1 ≤ k)
    (P : MvPolynomial (ι × Fin N) ℝ) (j : Fin N) :
    ∑ σ : ι → Equiv.Perm (Fin N), sgnP σ * (X (τ, (σ τ).symm j) ^ k * P).coeff (permExp σ) = 0 := by
  have hjN := j.isLt
  by_cases hjk : (j : ℕ) + k < N
  · have hne : j ≠ (⟨(j : ℕ) + k, hjk⟩ : Fin N) := by
      intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    refine sum_eq_zero_of_anti (Pi.mulSingle τ (Equiv.swap j ⟨(j : ℕ) + k, hjk⟩))
      (fun σ => sgnP σ * (X (τ, (σ τ).symm j) ^ k * P).coeff (permExp σ)) ?_
    intro σ
    have hsymm : ((Pi.mulSingle τ (Equiv.swap j ⟨(j : ℕ) + k, hjk⟩) * σ : ι → Equiv.Perm (Fin N)) τ).symm j =
        (σ τ).symm ⟨(j : ℕ) + k, hjk⟩ := by
      rw [Equiv.symm_apply_eq, Pi.mul_apply, Pi.mulSingle_eq_same, Equiv.Perm.mul_apply,
        Equiv.apply_symm_apply, Equiv.swap_apply_right]
    have hc : permExp (Pi.mulSingle τ (Equiv.swap j ⟨(j : ℕ) + k, hjk⟩) * σ)
        (τ, (σ τ).symm ⟨(j : ℕ) + k, hjk⟩) = permExp σ (τ, (σ τ).symm j) := by
      simp only [permExp_apply, mulSingle_mul_apply, if_true, Equiv.apply_symm_apply,
        Equiv.swap_apply_right]
    rw [hsymm, permSign_mulSingle_swap_mul τ _ _ hne, coeff_Xpow_mul, coeff_Xpow_mul, hc,
      rem_eq σ τ k j _ rfl hne]
    ring
  · refine Finset.sum_eq_zero fun σ _ => ?_
    rw [coeff_Xpow_mul, if_neg, mul_zero]
    simp only [permExp_apply, Equiv.apply_symm_apply]
    omega

theorem degFlPowerSum : DegFlPowerSum := by
  intro ι _ _ N τ k P hk
  unfold degFl
  rw [Finset.sum_mul]
  have h : ∀ σ : ι → Equiv.Perm (Fin N),
      (∏ t, ((Equiv.Perm.sign (σ t) : ℤ) : ℝ)) * (∑ i, X (τ, i) ^ k * P).coeff (permExp σ) =
        ∑ j : Fin N, sgnP σ * (X (τ, (σ τ).symm j) ^ k * P).coeff (permExp σ) := by
    intro σ
    rw [coeff_sum, Finset.mul_sum]
    exact (Equiv.sum_comp (σ τ).symm (fun i => sgnP σ * (X (τ, i) ^ k * P).coeff (permExp σ))).symm
  rw [Finset.sum_congr rfl (fun σ _ => h σ), Finset.sum_comm,
    Finset.sum_eq_zero (fun j _ => slice τ k hk P j), mul_zero]

theorem Z_mul_left {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} {Q : MvPolynomial (ι × Fin N) ℝ}
    (hQ : ∀ P, degFl ι N (Q * P) = 0) (R : MvPolynomial (ι × Fin N) ℝ) :
    ∀ P, degFl ι N ((R * Q) * P) = 0 := by
  intro P
  rw [mul_comm R Q, mul_assoc]
  exact hQ _

theorem Z_sum {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} {α : Type*} (s : Finset α)
    (g : α → MvPolynomial (ι × Fin N) ℝ) (h : ∀ a ∈ s, ∀ P, degFl ι N (g a * P) = 0) :
    ∀ P, degFl ι N ((∑ a ∈ s, g a) * P) = 0 := by
  intro P
  rw [Finset.sum_mul, degFl_sum]
  exact Finset.sum_eq_zero fun a ha => h a ha P

theorem degFlEsymm : DegFlEsymm := by
  intro ι _ _ N τ k P hk
  have hp : ∀ n, 1 ≤ n → ∀ P : MvPolynomial (ι × Fin N) ℝ,
      degFl ι N (rename (fun i : Fin N => (τ, i)) (psum (Fin N) ℝ n) * P) = 0 := by
    intro n hn P
    simp only [psum, map_sum, map_pow, rename_X]
    exact degFlPowerSum ι N τ n P hn
  have hZ : ∀ P : MvPolynomial (ι × Fin N) ℝ, degFl ι N (rename (fun i : Fin N => (τ, i))
      ((k : MvPolynomial (Fin N) ℝ) * esymm (Fin N) ℝ k) * P) = 0 := by
    rw [mul_esymm_eq_sum, map_mul]
    apply Z_mul_left
    rw [map_sum]
    apply Z_sum
    intro a ha
    rw [map_mul]
    apply Z_mul_left
    apply hp
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at ha1
    omega
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hCC : C (k : ℝ) * C (k : ℝ)⁻¹ = (1 : MvPolynomial (ι × Fin N) ℝ) := by
    rw [← map_mul, mul_inv_cancel₀ hk0, map_one]
  have e1 : rename (fun i : Fin N => (τ, i)) (esymm (Fin N) ℝ k) * P =
      rename (fun i : Fin N => (τ, i)) ((k : MvPolynomial (Fin N) ℝ) * esymm (Fin N) ℝ k) *
        (C (k : ℝ)⁻¹ * P) := by
    rw [map_mul, map_natCast, ← map_natCast (C : ℝ →+* MvPolynomial (ι × Fin N) ℝ) k]
    linear_combination (-(rename (fun i : Fin N => (τ, i)) (esymm (Fin N) ℝ k) * P)) * hCC
  rw [e1]
  exact hZ _

end Formalism.DegreeFormula.PPowSum

namespace Formalism.DegreeFormula

theorem degreePowerSumMulEqZero : DegFlPowerSum := PPowSum.degFlPowerSum
theorem degreeEsymmMulEqZero : DegFlEsymm := PPowSum.degFlEsymm
theorem degreeHomogeneousEqZero : DegFlHomog := PPowSum.degFlHomog

end Formalism.DegreeFormula
