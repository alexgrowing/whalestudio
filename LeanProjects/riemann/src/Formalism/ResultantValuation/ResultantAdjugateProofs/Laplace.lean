import Formalism.ResultantValuation.ResultantConjugate

open Finset Equiv

noncomputable section

namespace Formalism.ResultantValuation

namespace LaplaceProof

theorem perm_sign_eq_inversion_sign {n : ℕ} (f : Perm (Fin n)) : Perm.sign f = Perm.signAux f := by
  refine Perm.swap_induction_on f ?_ ?_
  · rw [map_one, Perm.signAux_one]
  · intro g x y hxy ih
    rw [Perm.sign_mul, Perm.signAux_mul, ih, Perm.sign_swap hxy, Perm.signAux_swap hxy]

theorem prod_finPairsLT {n : ℕ} (f : (Σ _ : Fin n, Fin n) → ℤˣ) :
    ∏ p ∈ Perm.finPairsLT n, f p = ∏ x : Fin n, ∏ y : Fin n, if y < x then f ⟨x, y⟩ else 1 := by
  have hs : Perm.finPairsLT n = univ.sigma (fun x : Fin n => univ.filter (· < x)) := by
    ext ⟨x, y⟩
    simp [Perm.mem_finPairsLT]
  rw [hs, Finset.prod_sigma]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Finset.prod_filter]

variable {a b : ℕ}

theorem shuffle_bijective (J : Finset (Fin (a + b))) (h : J.card = a) (hc : Jᶜ.card = b) :
    Function.Bijective (Sum.elim (J.orderEmbOfFin h) (Jᶜ.orderEmbOfFin hc)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp⟩
  rintro (i | i) (j | j) hij
  · simp only [Sum.elim_inl] at hij
    rw [(J.orderEmbOfFin h).injective hij]
  · simp only [Sum.elim_inl, Sum.elim_inr] at hij
    have h1 := J.orderEmbOfFin_mem h i
    rw [hij] at h1
    exact absurd h1 (Finset.mem_compl.mp (Jᶜ.orderEmbOfFin_mem hc j))
  · simp only [Sum.elim_inl, Sum.elim_inr] at hij
    have h1 := J.orderEmbOfFin_mem h j
    rw [← hij] at h1
    exact absurd h1 (Finset.mem_compl.mp (Jᶜ.orderEmbOfFin_mem hc i))
  · simp only [Sum.elim_inr] at hij
    rw [(Jᶜ.orderEmbOfFin hc).injective hij]

def shuffle (J : Finset (Fin (a + b))) (h : J.card = a) (hc : Jᶜ.card = b) : Perm (Fin (a + b)) :=
  finSumFinEquiv.symm.trans (Equiv.ofBijective _ (shuffle_bijective J h hc))

@[simp] theorem shuffle_castAdd (J : Finset (Fin (a + b))) (h : J.card = a) (hc : Jᶜ.card = b)
    (i : Fin a) : shuffle J h hc (Fin.castAdd b i) = J.orderEmbOfFin h i := by
  simp [shuffle]

@[simp] theorem shuffle_natAdd (J : Finset (Fin (a + b))) (h : J.card = a) (hc : Jᶜ.card = b)
    (j : Fin b) : shuffle J h hc (Fin.natAdd a j) = Jᶜ.orderEmbOfFin hc j := by
  simp [shuffle]

private lemma card_filter_le_orderEmbOfFin (J : Finset (Fin (a + b))) (h : J.card = a) (i : Fin a) :
    (J.filter (· ≤ J.orderEmbOfFin h i)).card = (i : ℕ) + 1 := by
  have hm : J.filter (· ≤ J.orderEmbOfFin h i) = (Finset.Iic i).map (J.orderEmbOfFin h).toEmbedding := by
    ext y
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_Iic]
    constructor
    · rintro ⟨hy, hyt⟩
      have hr : y ∈ Set.range (J.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]
        exact Finset.mem_coe.mpr hy
      obtain ⟨k, rfl⟩ := hr
      exact ⟨k, (J.orderEmbOfFin h).le_iff_le.mp hyt, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem _ _ _, (J.orderEmbOfFin h).le_iff_le.mpr hk⟩
  rw [hm, Finset.card_map, Fin.card_Iic]

theorem card_compl_le (J : Finset (Fin (a + b))) (h : J.card = a) (i : Fin a) :
    (Jᶜ.filter (· ≤ J.orderEmbOfFin h i)).card + (i : ℕ) = (J.orderEmbOfFin h i : ℕ) := by
  have h1 := card_filter_le_orderEmbOfFin J h i
  have h2 : (J.filter (· ≤ J.orderEmbOfFin h i)).card + (Jᶜ.filter (· ≤ J.orderEmbOfFin h i)).card
      = (Finset.Iic (J.orderEmbOfFin h i)).card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter disjoint_compl_right),
      ← Finset.filter_union, Finset.union_compl]
    congr 1
    ext y
    simp
  rw [Fin.card_Iic] at h2
  omega

private theorem perm_inversion_sign_eq_prod {n : ℕ} (g : Perm (Fin n)) :
    Perm.signAux g = ∏ x : Fin n, ∏ y : Fin n,
      if y < x then (if g x ≤ g y then (-1 : ℤˣ) else 1) else 1 := by
  rw [Perm.signAux.eq_1, prod_finPairsLT]
  all_goals rfl

private lemma prod_fin_add_lt_split (F : Fin (a + b) → Fin (a + b) → ℤˣ) :
    ∏ x : Fin (a + b), ∏ y : Fin (a + b), (if y < x then F x y else 1) =
      (∏ i : Fin a, ∏ i' : Fin a, if i' < i then F (Fin.castAdd b i) (Fin.castAdd b i') else 1) *
      ((∏ j : Fin b, ∏ i : Fin a, F (Fin.natAdd a j) (Fin.castAdd b i)) *
       (∏ j : Fin b, ∏ j' : Fin b, if j' < j then F (Fin.natAdd a j) (Fin.natAdd a j') else 1)) := by
  have hlt : ∀ (i : Fin a) (j : Fin b), (i : ℕ) < a + (j : ℕ) := fun i j => by
    have := i.isLt
    omega
  have hnlt : ∀ (i : Fin a) (j : Fin b), ¬ (a + (j : ℕ) < (i : ℕ)) := fun i j => by
    have := i.isLt
    omega
  simp only [Fin.prod_univ_add, Finset.prod_mul_distrib, Fin.lt_iff_val_lt_val, Fin.coe_castAdd,
    Fin.coe_natAdd, add_lt_add_iff_left, hlt, hnlt, ↓reduceIte, Finset.prod_const_one, mul_one, one_mul,
    mul_assoc]

private lemma card_filter_compl_orderEmbOfFin_le (J : Finset (Fin (a + b))) (hc : Jᶜ.card = b) (t : Fin (a + b)) :
    (univ.filter (fun j : Fin b => Jᶜ.orderEmbOfFin hc j ≤ t)).card = (Jᶜ.filter (· ≤ t)).card := by
  rw [← Finset.card_map (Jᶜ.orderEmbOfFin hc).toEmbedding]
  congr 1
  ext y
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Finset.orderEmbOfFin_mem _ _ _, hj⟩
  · rintro ⟨hy, hyt⟩
    have hr : y ∈ Set.range (Jᶜ.orderEmbOfFin hc) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr hy
    obtain ⟨j, rfl⟩ := hr
    exact ⟨j, hyt, rfl⟩

private lemma sum_val_eq_sum_orderEmbOfFin (J : Finset (Fin (a + b))) (h : J.card = a) :
    ∑ j ∈ J, (j : ℕ) = ∑ i : Fin a, (J.orderEmbOfFin h i : ℕ) := by
  have hJ : J = Finset.univ.map (J.orderEmbOfFin h).toEmbedding := by
    ext y
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · intro hy
      have hr : y ∈ Set.range (J.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]
        exact Finset.mem_coe.mpr hy
      obtain ⟨k, rfl⟩ := hr
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact Finset.orderEmbOfFin_mem _ _ _
  conv_lhs => rw [hJ]
  exact Finset.sum_map _ _ _

theorem sign_shuffle (J : Finset (Fin (a + b))) (h : J.card = a) (hc : Jᶜ.card = b) :
    Perm.sign (shuffle J h hc) = (-1) ^ (a * (a - 1) / 2 + ∑ j ∈ J, (j : ℕ)) := by
  rw [perm_sign_eq_inversion_sign, perm_inversion_sign_eq_prod, prod_fin_add_lt_split]
  have hA : (∏ i : Fin a, ∏ i' : Fin a, if i' < i then (if shuffle J h hc (Fin.castAdd b i) ≤
      shuffle J h hc (Fin.castAdd b i') then (-1 : ℤˣ) else 1) else 1) = 1 := by
    refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun i' _ => ?_
    split_ifs with h1 h2
    · rw [shuffle_castAdd, shuffle_castAdd, OrderEmbedding.le_iff_le] at h2
      exact absurd h2 (not_le.mpr h1)
    · rfl
    · rfl
  have hD : (∏ j : Fin b, ∏ j' : Fin b, if j' < j then (if shuffle J h hc (Fin.natAdd a j) ≤
      shuffle J h hc (Fin.natAdd a j') then (-1 : ℤˣ) else 1) else 1) = 1 := by
    refine Finset.prod_eq_one fun j _ => Finset.prod_eq_one fun j' _ => ?_
    split_ifs with h1 h2
    · rw [shuffle_natAdd, shuffle_natAdd, OrderEmbedding.le_iff_le] at h2
      exact absurd h2 (not_le.mpr h1)
    · rfl
    · rfl
  rw [hA, hD, one_mul, mul_one]
  simp only [shuffle_castAdd, shuffle_natAdd]
  rw [Finset.prod_comm]
  have hrow : ∀ i : Fin a, (∏ j : Fin b, if Jᶜ.orderEmbOfFin hc j ≤ J.orderEmbOfFin h i then
      (-1 : ℤˣ) else 1) = (-1) ^ (Jᶜ.filter (· ≤ J.orderEmbOfFin h i)).card := by
    intro i
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, card_filter_compl_orderEmbOfFin_le]
  refine (Finset.prod_congr rfl fun i _ => hrow i).trans ?_
  rw [Finset.prod_pow_eq_pow_sum, sum_val_eq_sum_orderEmbOfFin J h]
  have hsum : ∑ i : Fin a, (J.orderEmbOfFin h i : ℕ) =
      ∑ i : Fin a, (Jᶜ.filter (· ≤ J.orderEmbOfFin h i)).card + a * (a - 1) / 2 := by
    rw [← Finset.sum_range_id, ← Fin.sum_univ_eq_sum_range (fun i => i) a, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (card_compl_le J h i).symm
  rw [hsum]
  generalize (∑ i : Fin a, (Jᶜ.filter (· ≤ J.orderEmbOfFin h i)).card) = C
  generalize a * (a - 1) / 2 = T
  rw [show T + (C + T) = C + 2 * T by ring, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

theorem det_rows {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (M : Matrix n n R) : M.det = ∑ σ : Perm n, ((Perm.sign σ : ℤ) : R) * ∏ i, M i (σ i) := by
  rw [← M.det_transpose, Matrix.det_apply']
  simp only [Matrix.transpose_apply]

theorem compl_card (J : {J : Finset (Fin (a + b)) // J.card = a}) : (J.1ᶜ).card = b := by
  rw [Finset.card_compl, Fintype.card_fin, J.2]
  omega

def glue (x : Σ _ : {J : Finset (Fin (a + b)) // J.card = a}, Perm (Fin a) × Perm (Fin b)) :
    Perm (Fin (a + b)) :=
  shuffle x.1.1 x.1.2 (compl_card x.1) * finSumFinEquiv.permCongr (Perm.sumCongr x.2.1 x.2.2)

@[simp] theorem glue_castAdd (x : Σ _ : {J : Finset (Fin (a + b)) // J.card = a},
    Perm (Fin a) × Perm (Fin b)) (i : Fin a) :
    glue x (Fin.castAdd b i) = x.1.1.orderEmbOfFin x.1.2 (x.2.1 i) := by
  simp [glue, Equiv.permCongr_apply]

@[simp] theorem glue_natAdd (x : Σ _ : {J : Finset (Fin (a + b)) // J.card = a},
    Perm (Fin a) × Perm (Fin b)) (j : Fin b) :
    glue x (Fin.natAdd a j) = (x.1.1ᶜ).orderEmbOfFin (compl_card x.1) (x.2.2 j) := by
  simp [glue, Equiv.permCongr_apply]

theorem sign_glue (x : Σ _ : {J : Finset (Fin (a + b)) // J.card = a},
    Perm (Fin a) × Perm (Fin b)) :
    Perm.sign (glue x) = (-1) ^ (a * (a - 1) / 2 + ∑ j ∈ x.1.1, (j : ℕ)) *
      Perm.sign x.2.1 * Perm.sign x.2.2 := by
  simp only [glue, Perm.sign_mul, sign_shuffle, Perm.sign_permCongr, Perm.sign_sumCongr, mul_assoc]

theorem image_glue (x : Σ _ : {J : Finset (Fin (a + b)) // J.card = a},
    Perm (Fin a) × Perm (Fin b)) :
    univ.image (fun i => glue x (Fin.castAdd b i)) = x.1.1 := by
  simp only [glue_castAdd]
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact Finset.orderEmbOfFin_mem _ _ _
  · intro hy
    have hr : y ∈ Set.range (x.1.1.orderEmbOfFin x.1.2) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr hy
    obtain ⟨k, rfl⟩ := hr
    exact ⟨x.2.1.symm k, by simp⟩

theorem glue_injective : Function.Injective (glue (a := a) (b := b)) := by
  rintro ⟨⟨J, hJ⟩, σ, τ⟩ ⟨⟨J', hJ'⟩, σ', τ'⟩ heq
  have hJJ : J = J' := by
    have h1 := image_glue (⟨⟨J, hJ⟩, σ, τ⟩ : Σ _ : {J : Finset (Fin (a + b)) // J.card = a},
      Perm (Fin a) × Perm (Fin b))
    have h2 := image_glue (⟨⟨J', hJ'⟩, σ', τ'⟩ : Σ _ : {J : Finset (Fin (a + b)) // J.card = a},
      Perm (Fin a) × Perm (Fin b))
    rw [heq] at h1
    exact h1.symm.trans h2
  subst hJJ
  have hσ : σ = σ' := by
    refine Equiv.ext fun i => ?_
    have hi := congrArg (fun g : Perm (Fin (a + b)) => g (Fin.castAdd b i)) heq
    simp only [glue_castAdd] at hi
    exact (J.orderEmbOfFin hJ).injective hi
  have hτ : τ = τ' := by
    refine Equiv.ext fun j => ?_
    have hj := congrArg (fun g : Perm (Fin (a + b)) => g (Fin.natAdd a j)) heq
    simp only [glue_natAdd] at hj
    exact (Jᶜ.orderEmbOfFin (compl_card ⟨J, hJ⟩)).injective hj
  subst hσ
  subst hτ
  rfl

theorem glue_bijective : Function.Bijective (glue (a := a) (b := b)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨glue_injective, ?_⟩
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_finset_len]
  have key := Nat.add_choose_mul_factorial_mul_factorial b a
  rw [add_comm b a] at key
  rw [← key]
  ring

end LaplaceProof

open LaplaceProof in
theorem laplaceExpansionRows : LaplaceRows := by
  intro R _ a b M
  rw [det_rows M, ← (glue_bijective (a := a) (b := b)).sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [det_rows, det_rows, mul_assoc, Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [sign_glue, Fin.prod_univ_add]
  simp only [glue_castAdd, glue_natAdd, Matrix.submatrix_apply]
  push_cast
  ring

end Formalism.ResultantValuation
