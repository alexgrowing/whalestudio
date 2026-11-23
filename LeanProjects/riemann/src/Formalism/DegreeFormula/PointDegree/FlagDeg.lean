import Formalism.DegreeFormula.FlagDegFormula

noncomputable section

open MvPolynomial

namespace Formalism.DegreeFormula
namespace PFlagDeg

def sfac (N : ℕ) : ℕ := ∏ i : Fin N, (i : ℕ).factorial

lemma prod_perm_rev {M : Type*} [CommMonoid M] {N : ℕ} (s : Equiv.Perm (Fin N)) (g : ℕ → M) :
    ∏ i : Fin N, g (N - 1 - ((s i : Fin N) : ℕ)) = ∏ i : Fin N, g (i : ℕ) := by
  rw [Equiv.prod_comp s (fun j : Fin N => g (N - 1 - (j : ℕ)))]
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun i => ?_)
  simp only [Fin.revPerm_apply, Fin.val_rev]
  congr 1
  omega

lemma sum_perm_rev {N : ℕ} (s : Equiv.Perm (Fin N)) :
    ∑ i : Fin N, (N - 1 - ((s i : Fin N) : ℕ)) = ∑ i : Fin N, (i : ℕ) := by
  rw [Equiv.sum_comp s (fun j : Fin N => N - 1 - (j : ℕ))]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)
  simp only [Fin.revPerm_apply, Fin.val_rev]
  omega

lemma permExp_apply {ι : Type} [Fintype ι] {N : ℕ} (σ : ι → Equiv.Perm (Fin N)) (x : ι × Fin N) :
    permExp σ x = N - 1 - ((σ x.1 x.2 : Fin N) : ℕ) := by
  simp [permExp]

lemma permExp_sum' {ι : Type} [Fintype ι] {N : ℕ} (σ : ι → Equiv.Perm (Fin N)) :
    ∑ x : ι × Fin N, permExp σ x = dimFl ι N := by
  rw [Fintype.sum_prod_type]
  simp only [permExp_apply, sum_perm_rev]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id, Finset.sum_const,
    Finset.card_univ, smul_eq_mul]
  rfl

lemma linRoot_eq {ι : Type} [Fintype ι] {N : ℕ} (lam : ι → Fin N → ℝ) :
    linRoot lam = ∑ x : ι × Fin N, (-lam x.1 x.2) • (X x : MvPolynomial (ι × Fin N) ℝ) := by
  unfold linRoot
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_eq_C_mul, C_neg, neg_mul]

set_option maxRecDepth 4000 in

lemma coeff_pow {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (lam : ι → Fin N → ℝ)
    (σ : ι → Equiv.Perm (Fin N)) :
    (linRoot lam ^ dimFl ι N).coeff (permExp σ) =
      (-1) ^ dimFl ι N * (((dimFl ι N).factorial : ℝ) / ((sfac N : ℝ) ^ Fintype.card ι)) *
        ∏ τ, ∏ i : Fin N, lam τ i ^ (N - 1 - ((σ τ i : Fin N) : ℕ)) := by
  have hterm : ∀ k : ι × Fin N → ℕ,
      ((Nat.multinomial Finset.univ k : ℕ) : MvPolynomial (ι × Fin N) ℝ) *
          ∏ x, ((-lam x.1 x.2) • (X x : MvPolynomial (ι × Fin N) ℝ)) ^ k x =
        monomial (Finsupp.equivFunOnFinite.symm k)
          ((Nat.multinomial Finset.univ k : ℝ) * ∏ x, (-lam x.1 x.2) ^ k x) := by
    intro k
    rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), C_mul, map_prod]
    simp only [smul_pow, smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib, map_pow, map_natCast,
      Finsupp.coe_equivFunOnFinite_symm]
    ring
  have hsum : ∑ x : ι × Fin N, (N - 1 - ((σ x.1 x.2 : Fin N) : ℕ)) = dimFl ι N := by
    rw [← permExp_sum' σ]
    simp only [permExp_apply]
  have hfac : ∏ x : ι × Fin N, (N - 1 - ((σ x.1 x.2 : Fin N) : ℕ)).factorial =
      sfac N ^ Fintype.card ι := by
    rw [Fintype.prod_prod_type,
      Finset.prod_congr rfl (fun τ _ => prod_perm_rev (σ τ) Nat.factorial), Finset.prod_const,
      Finset.card_univ]
    rfl
  rw [linRoot_eq, Finset.sum_pow_eq_sum_piAntidiag, coeff_sum]
  simp only [hterm, coeff_monomial]
  rw [Finset.sum_eq_single (fun x : ι × Fin N => N - 1 - ((σ x.1 x.2 : Fin N) : ℕ))]
  · rw [if_pos (show Finsupp.equivFunOnFinite.symm
        (fun x : ι × Fin N => N - 1 - ((σ x.1 x.2 : Fin N) : ℕ)) = permExp σ from rfl)]
    have hm : ((Nat.multinomial Finset.univ
        (fun x : ι × Fin N => N - 1 - ((σ x.1 x.2 : Fin N) : ℕ)) : ℕ) : ℝ) =
        ((dimFl ι N).factorial : ℝ) / ((sfac N : ℝ) ^ Fintype.card ι) := by
      have hs := Nat.multinomial_spec Finset.univ
        (fun x : ι × Fin N => N - 1 - ((σ x.1 x.2 : Fin N) : ℕ))
      rw [hfac, hsum] at hs
      have hpos : ((sfac N : ℝ) ^ Fintype.card ι) ≠ 0 := by
        apply pow_ne_zero
        unfold sfac
        exact_mod_cast (Finset.prod_pos fun i _ => Nat.factorial_pos _).ne'
      rw [eq_div_iff hpos, mul_comm]
      exact_mod_cast hs
    have hp : ∏ x : ι × Fin N, (-lam x.1 x.2) ^ (N - 1 - ((σ x.1 x.2 : Fin N) : ℕ)) =
        (-1) ^ dimFl ι N * ∏ τ, ∏ i : Fin N, lam τ i ^ (N - 1 - ((σ τ i : Fin N) : ℕ)) := by
      rw [Finset.prod_congr rfl (fun x _ => neg_pow (lam x.1 x.2) (N - 1 - ((σ x.1 x.2 : Fin N) : ℕ))),
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum, Fintype.prod_prod_type]
    rw [hm, hp]
    ring
  · intro k _ hk
    rw [if_neg]
    intro h
    exact hk (Finsupp.equivFunOnFinite.symm.injective h)
  · intro h
    exfalso
    apply h
    rw [Finset.mem_piAntidiag]
    exact ⟨hsum, fun i _ => Finset.mem_univ i⟩

lemma pairs_rev {N : ℕ} (v : Fin N → ℝ) :
    ∏ i : Fin N, ∏ k : Fin N, (if i < k then v i - v k else 1) =
      ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v (Fin.rev j) - v (Fin.rev i)) := by
  calc ∏ i : Fin N, ∏ k : Fin N, (if i < k then v i - v k else 1)
      = ∏ i : Fin N, ∏ k : Fin N,
          (if Fin.rev i < Fin.rev k then v (Fin.rev i) - v (Fin.rev k) else 1) := by
        rw [← Equiv.prod_comp Fin.revPerm]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Equiv.prod_comp Fin.revPerm]
        rfl
    _ = ∏ k : Fin N, ∏ i : Fin N, (if k < i then v (Fin.rev i) - v (Fin.rev k) else 1) := by
        rw [Finset.prod_comm]
        simp only [Fin.rev_lt_rev]
    _ = _ := by
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [← Finset.filter_lt_eq_Ioi, Finset.prod_filter]

lemma vandermonde_sum {N : ℕ} (v : Fin N → ℝ) :
    ∑ s : Equiv.Perm (Fin N), ((Equiv.Perm.sign s : ℤ) : ℝ) *
        ∏ i, v i ^ (N - 1 - ((s i : Fin N) : ℕ)) =
      ∏ i : Fin N, ∏ k : Fin N, if i < k then v i - v k else 1 := by
  rw [pairs_rev, ← Matrix.det_vandermonde,
    ← Matrix.det_submatrix_equiv_self Fin.revPerm (Matrix.vandermonde fun i => v (Fin.rev i)),
    ← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.vandermonde_apply,
    Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  congr 1
  omega

lemma pairs_nat (N : ℕ) :
    ∏ i : Fin N, ∏ k : Fin N, (if i < k then ((k : ℝ) - (i : ℝ)) else 1) = (sfac N : ℝ) := by
  rw [Finset.prod_comm]
  unfold sfac
  push_cast
  refine Finset.prod_congr rfl fun k _ => ?_
  have h1 : ∀ i : Fin N, (if i < k then ((k : ℝ) - (i : ℝ)) else 1) =
      (fun m : ℕ => if m < (k : ℕ) then (((k : ℕ) : ℝ) - (m : ℝ)) else 1) (i : ℕ) := fun i => rfl
  rw [Finset.prod_congr rfl (fun i _ => h1 i),
    Fin.prod_univ_eq_prod_range (fun m : ℕ => if m < (k : ℕ) then (((k : ℕ) : ℝ) - (m : ℝ)) else 1) N,
    ← Finset.prod_range_mul_prod_Ico _ (le_of_lt k.2)]
  rw [Finset.prod_eq_one (s := Finset.Ico (k : ℕ) N)
    (fun i hi => by rw [Finset.mem_Ico] at hi; simp [not_lt.mpr hi.1]), mul_one]
  rw [← Finset.prod_range_reflect]
  have h2 : ∀ i ∈ Finset.range (k : ℕ),
      (if (k : ℕ) - 1 - i < (k : ℕ) then (((k : ℕ) : ℝ) - (((k : ℕ) - 1 - i : ℕ) : ℝ)) else 1) =
        ((i + 1 : ℕ) : ℝ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [if_pos (by omega)]
    rw [Nat.cast_sub (by omega : i ≤ (k : ℕ) - 1), Nat.cast_sub (by omega : 1 ≤ (k : ℕ))]
    push_cast
    ring
  rw [Finset.prod_congr rfl h2, ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]

end PFlagDeg

open PFlagDeg in
theorem flagDegFormula_statement : FlagDegFormula := by
  unfold FlagDegFormula
  intro ι _ _ N lam
  unfold flagDeg degFl weylProd
  simp only [coeff_pow]
  have hV : ∀ τ, ∏ i : Fin N, ∏ k : Fin N,
      (if i < k then (lam τ i - lam τ k) / ((k : ℝ) - (i : ℝ)) else 1) =
        (∏ i : Fin N, ∏ k : Fin N, if i < k then lam τ i - lam τ k else 1) / (sfac N : ℝ) := by
    intro τ
    rw [← pairs_nat N, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    split_ifs <;> simp
  have hsum : ∑ σ : ι → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) *
        ∏ τ, ∏ i : Fin N, lam τ i ^ (N - 1 - ((σ τ i : Fin N) : ℕ)) =
      ∏ τ, ∏ i : Fin N, ∏ k : Fin N, (if i < k then lam τ i - lam τ k else 1) := by
    rw [Finset.prod_congr rfl (fun τ _ => (vandermonde_sum (lam τ)).symm), Fintype.prod_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib]
  have hsq : ((-1 : ℝ) ^ dimFl ι N) * (-1) ^ dimFl ι N = 1 := by
    rw [← mul_pow]
    norm_num
  simp only [hV, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  rw [← hsum, Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  linear_combination ((∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) *
    (((dimFl ι N).factorial : ℝ) / ((sfac N : ℝ) ^ Fintype.card ι)) *
      ∏ τ, ∏ i : Fin N, lam τ i ^ (N - 1 - ((σ τ i : Fin N) : ℕ))) * hsq

end Formalism.DegreeFormula
