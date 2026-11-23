import Formalism.ArtinHasse.Statement

noncomputable section
open Finset

namespace Formalism.FT.SymmetricSeries

variable {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

lemma prod_map_X_eq_monomial (s : Multiset σ) :
    (s.map (MvPolynomial.X : σ → MvPolynomial σ R)).prod =
      MvPolynomial.monomial (Multiset.toFinsupp s) 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add, Multiset.toFinsupp_add,
      Multiset.toFinsupp_singleton, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]

lemma toFinsupp_sum (s : Multiset σ) : ∑ i, Multiset.toFinsupp s i = Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, ih, Finsupp.single_apply]
    simp [add_comm]

lemma hsymm_eq_sum_monomial (k : ℕ) :
    MvPolynomial.hsymm σ R k =
      ∑ l ∈ finsuppAntidiag (univ : Finset σ) k, MvPolynomial.monomial l 1 := by
  rw [MvPolynomial.hsymm]
  simp_rw [prod_map_X_eq_monomial]
  refine Finset.sum_bij' (fun s _ => Multiset.toFinsupp s.1)
    (fun l hl => ⟨Finsupp.toMultiset l, by
      rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact (Finset.mem_finsuppAntidiag.mp hl).1⟩) ?_ ?_ ?_ ?_ ?_
  · intro s _
    rw [Finset.mem_finsuppAntidiag]
    exact ⟨by rw [toFinsupp_sum]; exact s.2, Finset.subset_univ _⟩
  · intro l _
    exact Finset.mem_univ _
  · intro s _
    apply Subtype.ext
    simp
  · intro l _
    simp
  · intro s _
    rfl

open PowerSeries in
lemma geom_mul (a : R) : (1 - C a * X) * PowerSeries.mk (fun m => a ^ m) = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul]
  rcases n with _ | n
  · simp
  · rw [PowerSeries.coeff_succ_X_mul]
    simp [pow_succ, mul_comm]

end Formalism.FT.SymmetricSeries

namespace Formalism.FT.SymmetricSeries

variable {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

open PowerSeries in
lemma coeff_prod_one_sub (i : ℕ) :
    coeff i (∏ j : σ, (1 - C (MvPolynomial.X j : MvPolynomial σ R) * X)) =
      (-1) ^ i * MvPolynomial.esymm σ R i := by
  have h1 : ∏ j : σ, (1 - C (MvPolynomial.X j : MvPolynomial σ R) * X) =
      ∑ t ∈ (univ : Finset σ).powerset,
        C ((-1) ^ t.card * ∏ j ∈ t, (MvPolynomial.X j : MvPolynomial σ R)) * X ^ t.card := by
    simp_rw [sub_eq_add_neg]
    rw [Finset.prod_one_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.prod_neg, Finset.prod_mul_distrib, Finset.prod_const, ← map_prod, map_mul, map_pow,
      map_neg, map_one]
    ring
  rw [h1, map_sum]
  simp_rw [PowerSeries.coeff_C_mul_X_pow]
  rw [← Finset.sum_filter]
  have hf : ((univ : Finset σ).powerset.filter fun t => i = t.card) = (univ : Finset σ).powersetCard i := by
    rw [Finset.powersetCard_eq_filter]
    ext t
    simp [eq_comm]
  rw [hf, MvPolynomial.esymm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [(Finset.mem_powersetCard.mp ht).2]

open PowerSeries in
lemma coeff_prod_geom (k : ℕ) :
    coeff k (∏ j : σ, PowerSeries.mk (fun m => (MvPolynomial.X j : MvPolynomial σ R) ^ m)) =
      MvPolynomial.hsymm σ R k := by
  rw [PowerSeries.coeff_prod, hsymm_eq_sum_monomial]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [PowerSeries.coeff_mk]
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem esymm_hsymm_rel (k : ℕ) (hk : 1 ≤ k) :
    ∑ i ∈ range (k + 1), (-1) ^ i * MvPolynomial.esymm σ R i * MvPolynomial.hsymm σ R (k - i) = 0 := by
  have hAB : (∏ j : σ, (1 - PowerSeries.C (MvPolynomial.X j : MvPolynomial σ R) * PowerSeries.X)) *
      (∏ j : σ, PowerSeries.mk (fun m => (MvPolynomial.X j : MvPolynomial σ R) ^ m)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun j _ => geom_mul _
  have h := congrArg (PowerSeries.coeff k) hAB
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, PowerSeries.coeff_one,
    if_neg (by omega)] at h
  simp only [coeff_prod_one_sub, coeff_prod_geom] at h
  exact h

end Formalism.FT.SymmetricSeries

namespace Formalism.FT.SymmetricSeries

variable (R : Type*) [CommRing R] (n : ℕ)

def yv (m : ℕ) : MvPolynomial (Fin n) R :=
  if h : 1 ≤ m ∧ m ≤ n then MvPolynomial.X ⟨m - 1, by omega⟩ else 0

def tri : ℕ → MvPolynomial (Fin n) R
  | 0 => 1
  | k + 1 => ∑ i : Fin (k + 1), (-1) ^ (i : ℕ) * yv R n (i + 1) * tri (k - i)
decreasing_by omega

variable {R n}

lemma tri_succ (k : ℕ) : tri R n (k + 1) =
    ∑ i ∈ range (k + 1), (-1) ^ i * yv R n (i + 1) * tri R n (k - i) := by
  rw [tri]
  exact Fin.sum_univ_eq_sum_range (fun i => (-1) ^ i * yv R n (i + 1) * tri R n (k - i)) (k + 1)

lemma aeval_tri {S : Type*} [CommRing S] [Algebra R S] (e h : ℕ → S) (he0 : e 0 = 1)
    (hh0 : h 0 = 1)
    (rel : ∀ k, 1 ≤ k → k ≤ n → ∑ i ∈ range (k + 1), (-1) ^ i * e i * h (k - i) = 0) :
    ∀ k, k ≤ n → MvPolynomial.aeval (fun j : Fin n => e (j + 1)) (tri R n k) = h k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases k with _ | k
    · rw [tri, map_one, hh0]
    · rw [tri_succ, map_sum]
      have hrel := rel (k + 1) (by omega) hk
      rw [Finset.sum_range_succ'] at hrel
      simp only [pow_zero, one_mul, he0, Nat.sub_zero] at hrel
      have hterm : ∀ i ∈ range (k + 1),
          MvPolynomial.aeval (fun j : Fin n => e (j + 1)) ((-1) ^ i * yv R n (i + 1) * tri R n (k - i)) =
            -((-1) ^ (i + 1) * e (i + 1) * h (k + 1 - (i + 1))) := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [map_mul, map_mul, map_pow, map_neg, map_one, ih (k - i) (by omega) (by omega)]
        have hy : MvPolynomial.aeval (fun j : Fin n => e (j + 1)) (yv R n (i + 1)) = e (i + 1) := by
          simp only [yv]
          rw [dif_pos (by omega)]
          simp
        rw [hy, show k + 1 - (i + 1) = k - i by omega, pow_succ]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
      linear_combination -hrel

lemma rel_swap {S : Type*} [CommRing S] (e h : ℕ → S) (k : ℕ)
    (H : ∑ i ∈ range (k + 1), (-1) ^ i * e i * h (k - i) = 0) :
    ∑ i ∈ range (k + 1), (-1) ^ i * h i * e (k - i) = 0 := by
  have h1 := Finset.sum_range_reflect (fun i => (-1 : S) ^ i * e i * h (k - i)) (k + 1)
  rw [H] at h1
  have h2 : ∑ i ∈ range (k + 1), (-1) ^ i * h i * e (k - i) =
      (-1) ^ k * ∑ j ∈ range (k + 1), (fun i => (-1 : S) ^ i * e i * h (k - i)) (k + 1 - 1 - j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp only [show k + 1 - 1 - j = k - j by omega, show k - (k - j) = j by omega]
    have hk : (-1 : S) ^ k = (-1) ^ (k - j) * (-1) ^ j := by
      rw [← pow_add, show k - j + j = k by omega]
    have hsq : ((-1 : S) ^ (k - j)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    rw [hk]
    linear_combination (-((-1 : S) ^ j * h j * e (k - j))) * hsq
  rw [h2, h1, mul_zero]

variable (R n)

def Ee : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  MvPolynomial.aeval (fun j : Fin n => MvPolynomial.esymm (Fin n) R (j + 1))
def Eh : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  MvPolynomial.aeval (fun j : Fin n => MvPolynomial.hsymm (Fin n) R (j + 1))
def Tt : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  MvPolynomial.aeval (fun j : Fin n => tri R n (j + 1))

variable {R n}

lemma Ee_injective : Function.Injective (Ee R n) := by
  intro p q h
  apply MvPolynomial.esymmAlgHom_fin_injective R (le_refl n)
  apply Subtype.ext
  rw [MvPolynomial.esymmAlgHom_apply, MvPolynomial.esymmAlgHom_apply]
  exact h

lemma Ee_comp_Tt : (Ee R n).comp (Tt R n) = Eh R n := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, Tt, Ee, Eh, MvPolynomial.aeval_X]
  exact aeval_tri (fun i => MvPolynomial.esymm (Fin n) R i) (fun i => MvPolynomial.hsymm (Fin n) R i)
    (MvPolynomial.esymm_zero _ _) (MvPolynomial.hsymm_zero _ _)
    (fun k hk _ => esymm_hsymm_rel k hk) (j + 1) (by have := j.isLt; omega)

lemma Eh_comp_Tt : (Eh R n).comp (Tt R n) = Ee R n := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, Tt, Ee, Eh, MvPolynomial.aeval_X]
  exact aeval_tri (fun i => MvPolynomial.hsymm (Fin n) R i) (fun i => MvPolynomial.esymm (Fin n) R i)
    (MvPolynomial.hsymm_zero _ _) (MvPolynomial.esymm_zero _ _)
    (fun k hk _ => rel_swap _ _ k (esymm_hsymm_rel k hk)) (j + 1) (by have := j.isLt; omega)

lemma Tt_Tt (q : MvPolynomial (Fin n) R) : Tt R n (Tt R n q) = q := by
  apply Ee_injective
  have h1 : (Ee R n).comp ((Tt R n).comp (Tt R n)) = Ee R n := by
    rw [← AlgHom.comp_assoc, Ee_comp_Tt, Eh_comp_Tt]
  exact congrArg (fun φ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R => φ q) h1

theorem Eh_injective : Function.Injective (Eh R n) := by
  intro p q h
  have e1 : ∀ x, Ee R n (Tt R n x) = Eh R n x := fun x => by rw [← AlgHom.comp_apply, Ee_comp_Tt]
  have h1 : Ee R n (Tt R n p) = Ee R n (Tt R n q) := by rw [e1, e1, h]
  have h2 := Ee_injective h1
  rw [← Tt_Tt p, ← Tt_Tt q, h2]

theorem Eh_surj (p : MvPolynomial (Fin n) R) (hp : p.IsSymmetric) : ∃ q, Eh R n q = p := by
  obtain ⟨q, hq⟩ := MvPolynomial.esymmAlgHom_fin_surjective R (le_refl n)
    (⟨p, (MvPolynomial.mem_symmetricSubalgebra p).mpr hp⟩ : MvPolynomial.symmetricSubalgebra (Fin n) R)
  refine ⟨Tt R n q, ?_⟩
  have e1 : ∀ x, Ee R n (Tt R n x) = Eh R n x := fun x => by rw [← AlgHom.comp_apply, Ee_comp_Tt]
  rw [← e1, Tt_Tt]
  have h1 := congrArg Subtype.val hq
  rw [MvPolynomial.esymmAlgHom_apply] at h1
  exact h1

end Formalism.FT.SymmetricSeries

namespace Formalism.FT.SymmetricSeries

variable {R : Type*} [CommRing R] {n : ℕ}

lemma hsymm_isHomogeneous (k : ℕ) : (MvPolynomial.hsymm (Fin n) R k).IsHomogeneous k := by
  rw [hsymm_eq_sum_monomial]
  apply MvPolynomial.IsHomogeneous.sum
  intro l hl
  apply MvPolynomial.isHomogeneous_monomial
  rw [Finsupp.degree_eq_sum]
  exact (Finset.mem_finsuppAntidiag.mp hl).1

variable (R n) in
abbrev hv : Fin n → MvPowerSeries (Fin n) R := fun j => Formalism.FT.hPS R n (j.val + 1)

lemma hasSubst_hv : MvPowerSeries.HasSubst (hv R n) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro j
  simp only [hv, Formalism.FT.hPS]
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
  exact (hsymm_isHomogeneous _).coeff_eq_zero (by simp)

def wt (α : Fin n →₀ ℕ) : ℕ := ∑ j : Fin n, ((j : ℕ) + 1) * α j

lemma prodpow_eq (α : Fin n →₀ ℕ) : α.prod (fun j e => hv R n j ^ e) =
    ((∏ j : Fin n, (MvPolynomial.hsymm (Fin n) R (j + 1)) ^ (α j) : MvPolynomial (Fin n) R) :
      MvPowerSeries (Fin n) R) := by
  unfold hv Formalism.FT.hPS
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have h := map_prod (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := R))
    (fun j : Fin n => MvPolynomial.hsymm (Fin n) R (j + 1) ^ α j) univ
  simp only [map_pow, MvPolynomial.coeToMvPowerSeries.ringHom_apply] at h
  exact h.symm

lemma prodpow_hom (α : Fin n →₀ ℕ) :
    (∏ j : Fin n, (MvPolynomial.hsymm (Fin n) R (j + 1)) ^ (α j)).IsHomogeneous (wt α) := by
  unfold wt
  apply MvPolynomial.IsHomogeneous.prod
  intro j _
  exact (hsymm_isHomogeneous _).pow _

lemma coeff_prodpow_eq_zero (α d : Fin n →₀ ℕ) (h : wt α ≠ d.degree) :
    MvPowerSeries.coeff d (α.prod (fun j e => hv R n j ^ e)) = 0 := by
  rw [prodpow_eq, MvPolynomial.coeff_coe]
  exact (prodpow_hom α).coeff_eq_zero (Ne.symm h)

lemma coe_Eh (P : MvPolynomial (Fin n) R) :
    ((Eh R n P : MvPolynomial (Fin n) R) : MvPowerSeries (Fin n) R) =
      MvPowerSeries.subst (hv R n) (P : MvPowerSeries (Fin n) R) := by
  rw [MvPowerSeries.subst_coe]
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, MvPowerSeries.algebraMap_apply]
    simp [Eh]
  | add p q hp hq => rw [map_add, MvPolynomial.coe_add, hp, hq, map_add]
  | mul_X p j hp =>
    rw [map_mul, MvPolynomial.coe_mul, hp, map_mul]
    congr 1
    simp [Eh, hv, Formalism.FT.hPS]

lemma coeff_Eh (P : MvPolynomial (Fin n) R) (d : Fin n →₀ ℕ) :
    MvPolynomial.coeff d (Eh R n P) =
      ∑ᶠ α, MvPolynomial.coeff α P • MvPowerSeries.coeff d (α.prod fun j e => hv R n j ^ e) := by
  rw [← MvPolynomial.coeff_coe, coe_Eh, MvPowerSeries.coeff_subst hasSubst_hv]
  simp only [MvPolynomial.coeff_coe]

end Formalism.FT.SymmetricSeries

namespace Formalism.FT.SymmetricSeries

variable {R : Type*} [CommRing R] {n : ℕ}

lemma prod_X_perm (π : Equiv.Perm (Fin n)) (e : Fin n →₀ ℕ) :
    e.prod (fun s k => (MvPowerSeries.X (π s) : MvPowerSeries (Fin n) R) ^ k) =
      MvPowerSeries.monomial (e.mapDomain π) 1 := by
  induction e using Finsupp.induction with
  | zero => simp
  | single_add a b f ha hb ih =>
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), ih,
      Finsupp.prod_single_index (h := fun s k => (MvPowerSeries.X (π s) : MvPowerSeries (Fin n) R) ^ k)
        (pow_zero _), MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial,
      mul_one, Finsupp.mapDomain_add, Finsupp.mapDomain_single]

lemma coeff_mapDomain_of_symm (F : MvPowerSeries (Fin n) R)
    (hF : ∀ π : Equiv.Perm (Fin n),
      F.subst (fun i => (MvPowerSeries.X (π i) : MvPowerSeries (Fin n) R)) = F)
    (π : Equiv.Perm (Fin n)) (d : Fin n →₀ ℕ) :
    MvPowerSeries.coeff (d.mapDomain π) F = MvPowerSeries.coeff d F := by
  have hs : MvPowerSeries.HasSubst (fun i => (MvPowerSeries.X (π i) : MvPowerSeries (Fin n) R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => MvPowerSeries.constantCoeff_X _)
  have h := congrArg (MvPowerSeries.coeff (d.mapDomain π)) (hF π)
  rw [MvPowerSeries.coeff_subst hs] at h
  simp_rw [prod_X_perm, MvPowerSeries.coeff_monomial,
    (Finsupp.mapDomain_injective π.injective).eq_iff, smul_ite, smul_zero, smul_eq_mul, mul_one] at h
  rw [← h, finsum_eq_single _ d (fun e he => if_neg (Ne.symm he))]
  simp

def Fm (F : MvPowerSeries (Fin n) R) (m : ℕ) : MvPolynomial (Fin n) R :=
  ∑ d ∈ finsuppAntidiag (univ : Finset (Fin n)) m, MvPolynomial.monomial d (MvPowerSeries.coeff d F)

lemma coeff_Fm (F : MvPowerSeries (Fin n) R) (m : ℕ) (d : Fin n →₀ ℕ) :
    MvPolynomial.coeff d (Fm F m) = if d.degree = m then MvPowerSeries.coeff d F else 0 := by
  unfold Fm
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : d.degree = m
  · rw [if_pos h, if_pos]
    rw [Finset.mem_finsuppAntidiag]
    exact ⟨by rw [← h, Finsupp.degree_eq_sum], Finset.subset_univ _⟩
  · rw [if_neg h, if_neg]
    rw [Finset.mem_finsuppAntidiag]
    rintro ⟨h1, _⟩
    exact h (by rw [Finsupp.degree_eq_sum]; exact h1)

lemma Fm_symm (F : MvPowerSeries (Fin n) R)
    (hF : ∀ π : Equiv.Perm (Fin n),
      F.subst (fun i => (MvPowerSeries.X (π i) : MvPowerSeries (Fin n) R)) = F)
    (m : ℕ) : (Fm F m).IsSymmetric := by
  intro π
  ext d
  have hd : d = (d.mapDomain π.symm).mapDomain π := by
    rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  have hdeg : (d.mapDomain π.symm).degree = d.degree := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, ← Equiv.sum_comp π.symm]
    simp [Finsupp.mapDomain_apply π.symm.injective]
  conv_lhs => rw [hd]
  rw [MvPolynomial.coeff_rename_mapDomain π π.injective, coeff_Fm, coeff_Fm,
    coeff_mapDomain_of_symm F hF π.symm d, hdeg]

theorem exists_G (F : MvPowerSeries (Fin n) R)
    (hF : ∀ π : Equiv.Perm (Fin n),
      F.subst (fun i => (MvPowerSeries.X (π i) : MvPowerSeries (Fin n) R)) = F) :
    ∃ G : MvPowerSeries (Fin n) R, G.subst (hv R n) = F := by
  choose q hq using fun m => Eh_surj (Fm F m) (Fm_symm F hF m)
  let G : MvPowerSeries (Fin n) R := fun α => MvPolynomial.coeff α (q (wt α))
  refine ⟨G, ?_⟩
  ext d
  rw [MvPowerSeries.coeff_subst hasSubst_hv G d]
  have h2 : MvPowerSeries.coeff d F = MvPolynomial.coeff d (Eh R n (q d.degree)) := by
    rw [hq, coeff_Fm, if_pos rfl]
  rw [h2, coeff_Eh]
  apply finsum_congr
  intro α
  by_cases h : wt α = d.degree
  · show MvPolynomial.coeff α (q (wt α)) • _ = _
    rw [h]
  · rw [coeff_prodpow_eq_zero α d h, smul_zero, smul_zero]

def Aw (n m : ℕ) : Finset (Fin n →₀ ℕ) :=
  ((range (m + 1)).biUnion fun k => finsuppAntidiag (univ : Finset (Fin n)) k).filter
    (fun α => wt α = m)

lemma mem_Aw (m : ℕ) (α : Fin n →₀ ℕ) : α ∈ Aw n m ↔ wt α = m := by
  unfold Aw
  rw [Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨∑ j, α j, ?_, ?_⟩, h⟩
    · rw [Finset.mem_range, Nat.lt_succ_iff, ← h]
      unfold wt
      exact Finset.sum_le_sum fun j _ => Nat.le_mul_of_pos_left _ (by omega)
    · rw [Finset.mem_finsuppAntidiag]
      exact ⟨rfl, Finset.subset_univ _⟩

theorem G_unique (H : MvPowerSeries (Fin n) R) (hH : H.subst (hv R n) = 0) : H = 0 := by
  ext α
  rw [map_zero]
  obtain ⟨m, hm⟩ : ∃ m, wt α = m := ⟨_, rfl⟩
  let P : MvPolynomial (Fin n) R := ∑ β ∈ Aw n m, MvPolynomial.monomial β (MvPowerSeries.coeff β H)
  have hcP : ∀ β, MvPolynomial.coeff β P = if wt β = m then MvPowerSeries.coeff β H else 0 := by
    intro β
    simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    by_cases h : wt β = m
    · rw [if_pos ((mem_Aw m β).mpr h), if_pos h]
    · rw [if_neg (fun h' => h ((mem_Aw m β).mp h')), if_neg h]
  have hEP : Eh R n P = 0 := by
    ext d
    rw [MvPolynomial.coeff_zero, coeff_Eh]
    by_cases hd : d.degree = m
    · have h0 := congrArg (MvPowerSeries.coeff d) hH
      rw [MvPowerSeries.coeff_subst hasSubst_hv, map_zero] at h0
      refine Eq.trans ?_ h0
      apply finsum_congr
      intro β
      rw [hcP]
      by_cases hb : wt β = m
      · rw [if_pos hb]
      · rw [if_neg hb, zero_smul, coeff_prodpow_eq_zero β d (by rw [hd]; exact hb), smul_zero]
    · apply finsum_eq_zero_of_forall_eq_zero
      intro β
      rw [hcP]
      by_cases hb : wt β = m
      · rw [if_pos hb, coeff_prodpow_eq_zero β d (by rw [hb]; exact Ne.symm hd), smul_zero]
      · rw [if_neg hb, zero_smul]
  have hP0 : P = 0 := Eh_injective (by rw [hEP, map_zero])
  have h1 := hcP α
  rw [hP0, MvPolynomial.coeff_zero, if_pos hm] at h1
  exact h1.symm

end Formalism.FT.SymmetricSeries

theorem Formalism.FT.symmetric_series_h_symm : Formalism.FT.SymmSeriesHsymm := by
  intro R _ n F hF
  obtain ⟨G, hG⟩ := Formalism.FT.SymmetricSeries.exists_G F hF
  refine ⟨G, hG, fun G' hG' => ?_⟩
  have hG'' : G'.subst (Formalism.FT.SymmetricSeries.hv R n) = F := hG'
  have h0 : (G' - G).subst (Formalism.FT.SymmetricSeries.hv R n) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom Formalism.FT.SymmetricSeries.hasSubst_hv, map_sub,
      MvPowerSeries.coe_substAlgHom Formalism.FT.SymmetricSeries.hasSubst_hv, hG'', hG, sub_self]
  exact sub_eq_zero.mp (Formalism.FT.SymmetricSeries.G_unique _ h0)
