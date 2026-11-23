import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HermMatrixMulVecFirst

noncomputable section

open Matrix MeasureTheory
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace FormulaFAux

theorem sg_eI (k r : ℕ) (a : Fin r) : sg k r (eI k r a) = esI k r a := by
  have ha := a.isLt
  unfold sg
  rw [if_neg (by simp only [eI, Fin.val_mk]; omega)]
  rfl

theorem hpk_es (k r : ℕ) (a : Fin r) : Hpk k r *ᵥ bvec (esI k r a) = bvec (eI k r a) := by
  ext i
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  simp only [Hpk, esI, eI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem Hpk_mulVec_apply_eq_ite (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (v : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ y) v = if (v : ℕ) < r ∨ r + k < (v : ℕ) then y ⟨2 * r + k - v, by omega⟩
      else if (v : ℕ) = r + k then -y v else y v := by
  have hv := v.isLt
  simp only [Matrix.mulVec, dotProduct]
  by_cases h1 : (v : ℕ) < r ∨ r + k < (v : ℕ)
  · rw [if_pos h1, Finset.sum_eq_single ⟨2 * r + k - v, by omega⟩]
    · rcases h1 with h1 | h1
      · simp only [Hpk, Fin.val_mk]
        rw [if_pos ⟨h1, by omega⟩, one_mul]
      · simp only [Hpk, Fin.val_mk]
        rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, one_mul]
    · intro j _ hj
      have hj' : (j : ℕ) ≠ 2 * r + k - v := fun e => hj (Fin.ext e)
      simp only [Hpk]
      rw [if_neg (by omega), if_neg (by omega), if_neg (fun hc => by have := hc.1; have := hc.2.1; omega),
        zero_mul]
    · simp
  · rw [if_neg h1, Finset.sum_eq_single v]
    · simp only [Hpk]
      rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, by trivial⟩]
      by_cases h2 : (v : ℕ) = r + k
      · rw [if_pos h2, if_pos h2, neg_one_mul]
      · rw [if_neg h2, if_neg h2, one_mul]
    · intro j _ hj
      simp only [Hpk]
      rw [if_neg (by omega), if_neg (fun hc => by have := hc.1; have := hc.2; omega),
        if_neg (fun hc => hj hc.2.2.symm), zero_mul]
    · simp

theorem hpk_hpk (k r : ℕ) (u : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ u) = u := by
  funext v
  have hv := v.isLt
  by_cases h1 : (v : ℕ) < r ∨ r + k < (v : ℕ)
  · rw [Hpk_mulVec_apply_eq_ite, if_pos h1, Hpk_mulVec_apply_eq_ite, if_pos (by simp only [Fin.val_mk]; omega)]
    congr 1
    ext
    simp only [Fin.val_mk]
    omega
  · rw [Hpk_mulVec_apply_eq_ite, if_neg h1]
    by_cases h2 : (v : ℕ) = r + k
    · rw [if_pos h2, Hpk_mulVec_apply_eq_ite, if_neg h1, if_pos h2, neg_neg]
    · rw [if_neg h2, Hpk_mulVec_apply_eq_ite, if_neg h1, if_neg h2]

theorem herm_symm (k r : ℕ) (u w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) u w = star (herm (Hpk k r) w u) := by
  have hsym : ∀ i j, Hpk k r i j = Hpk k r j i := by
    intro i j
    simp only [Hpk, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hstar : ∀ i j, star (Hpk k r i j) = Hpk k r i j := by
    intro i j
    simp only [Hpk]
    split_ifs <;> simp
  simp only [herm, dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, hstar,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsym]
  ring

theorem lift_kills_first_basis (k r' : ℕ) (w : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' w (eI k (1 + r') (a0 r')) = 0 := by
  unfold liftVec
  rw [dif_neg (by simp only [eI, a0, Fin.val_mk]; omega)]

theorem lift_kills_last_basis (k r' : ℕ) (w : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' w (esI k (1 + r') (a0 r')) = 0 := by
  unfold liftVec
  rw [dif_neg (by simp only [esI, a0, Fin.val_mk]; omega)]

theorem isotropic_vector_ne_zero (k r' : ℕ) : eI k (1 + r') (a0 r') ≠ esI k (1 + r') (a0 r') := by
  intro h
  have h' := congrArg Fin.val h
  simp only [eI, esI, a0, Fin.val_mk] at h'
  omega

@[simp] theorem d_es_es (k r' : ℕ) : star (es0 k r') ⬝ᵥ es0 k r' = 1 := by
  simp [es0, bvec, Pi.single_apply]
@[simp] theorem d_e_e (k r' : ℕ) : star (e0 k r') ⬝ᵥ e0 k r' = 1 := by
  simp [e0, bvec, Pi.single_apply]
@[simp] theorem d_es_e (k r' : ℕ) : star (es0 k r') ⬝ᵥ e0 k r' = 0 := by
  simp [es0, e0, bvec, Pi.single_apply, isotropic_vector_ne_zero k r']
@[simp] theorem d_e_es (k r' : ℕ) : star (e0 k r') ⬝ᵥ es0 k r' = 0 := by
  simp [es0, e0, bvec, Pi.single_apply, (isotropic_vector_ne_zero k r').symm]
@[simp] theorem d_es_l (k r' : ℕ) (w : Fin (2 * r' + k + 1) → ℂ) : star (es0 k r') ⬝ᵥ liftVec k 1 r' w = 0 := by
  have h := lift_kills_last_basis k r' w
  simp [es0, bvec, Pi.single_apply, dotProduct, h]
@[simp] theorem d_e_l (k r' : ℕ) (w : Fin (2 * r' + k + 1) → ℂ) : star (e0 k r') ⬝ᵥ liftVec k 1 r' w = 0 := by
  have h := lift_kills_first_basis k r' w
  simp [e0, bvec, Pi.single_apply, dotProduct, h]
@[simp] theorem d_l_es (k r' : ℕ) (w : Fin (2 * r' + k + 1) → ℂ) : star (liftVec k 1 r' w) ⬝ᵥ es0 k r' = 0 := by
  have h := lift_kills_last_basis k r' w
  simp [es0, bvec, Pi.single_apply, dotProduct, h]
@[simp] theorem d_l_e (k r' : ℕ) (w : Fin (2 * r' + k + 1) → ℂ) : star (liftVec k 1 r' w) ⬝ᵥ e0 k r' = 0 := by
  have h := lift_kills_first_basis k r' w
  simp [e0, bvec, Pi.single_apply, dotProduct, h]

theorem phiV_zero (k r' : ℕ) (h : 0 < 1 + r' + 1) : phiV k (1 + r') ⟨0, h⟩ = es0 k r' := by
  show (if h' : (0 : ℕ) < 1 + r' then bvec (esI k (1 + r') ⟨0, h'⟩) else epsV k (1 + r')) =
    bvec (esI k (1 + r') (a0 r'))
  rw [dif_pos (by omega)]
  rfl

private theorem sum_herm_bvec_mul_eq_herm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    ∑ j, herm H (bvec j) v * u j = herm H u v := by
  simp only [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem heisG_mulVec_eq (k r' : ℕ) (v u : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ) :
    heisG k r' v b *ᵥ u = u - (∑ j, herm (Hpk k (1 + r')) (bvec j) v * u j) • e0 k r' +
      (∑ j, herm (Hpk k (1 + r')) (bvec j) (e0 k r') * u j) • (v + b • e0 k r') := by
  ext i
  rw [heisG, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Matrix.vecMulVec_apply]
  rw [Finset.sum_mul, Finset.sum_mul]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  · exact Finset.sum_congr rfl fun j _ => by ring

theorem heisenberg_dual_base_vector_formula (k r' : ℕ) (x : HPar k r') :
    heis0 k r' x *ᵥ es0 k r' = es0 k r' + liftVec k 1 r' x.1 + hb k r' x.1 x.2 • e0 k r' := by
  rw [heis0, heisG_mulVec_eq, sum_herm_bvec_mul_eq_herm, sum_herm_bvec_mul_eq_herm]
  have h1 : herm (Hpk k (1 + r')) (es0 k r') (liftVec k 1 r' x.1) = 0 := by
    rw [herm, es0, hpk_es]
    exact d_l_e k r' x.1
  have h2 : herm (Hpk k (1 + r')) (es0 k r') (e0 k r') = 1 := by
    rw [herm, es0, hpk_es]
    exact d_e_e k r'
  rw [h1, h2, zero_smul, sub_zero, one_smul, ← add_assoc]

private theorem liftVec_apply_mk_succ (k r' : ℕ) (w : Fin (2 * r' + k + 1) → ℂ) (q : Fin (2 * r' + k + 1))
    (h : (q : ℕ) + 1 < 2 * (1 + r') + k + 1) : liftVec k 1 r' w ⟨(q : ℕ) + 1, h⟩ = w q := by
  unfold liftVec
  rw [dif_pos (by simp only [Fin.val_mk]; omega)]
  congr 1
  all_goals (ext; simp only [Fin.val_mk]; omega)

private theorem star_liftVec_dotProduct_liftVec (k r' : ℕ) (a b : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k 1 r' a) ⬝ᵥ liftVec k 1 r' b = star a ⬝ᵥ b := by
  unfold dotProduct
  symm
  refine Fintype.sum_of_injective (fun q : Fin (2 * r' + k + 1) => (⟨(q : ℕ) + 1, by omega⟩ : Fin (2 * (1 + r') + k + 1)))
    (fun q1 q2 h => Fin.ext (by have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)) _ _ ?_ ?_
  · intro p hp
    have hp' : ¬ (1 ≤ (p : ℕ) ∧ (p : ℕ) < 2 * r' + k + 1 + 1) := by
      rintro ⟨h1, h2⟩
      exact hp ⟨⟨(p : ℕ) - 1, by omega⟩, Fin.ext (by simp only [Fin.val_mk]; omega)⟩
    simp only [Pi.star_apply]
    unfold liftVec
    rw [dif_neg hp', dif_neg hp', star_zero, zero_mul]
  · intro q
    simp only [Pi.star_apply]
    rw [liftVec_apply_mk_succ, liftVec_apply_mk_succ]

private theorem Hpk_one_add_mulVec_liftVec (k r' : ℕ) (w : Fin (2 * r' + k + 1) → ℂ) :
    Hpk k (1 + r') *ᵥ liftVec k 1 r' w = liftVec k 1 r' (Hpk k r' *ᵥ w) := by
  funext p
  have hp := p.isLt
  simp only [Hpk_mulVec_apply_eq_ite, liftVec]
  split_ifs <;> (try simp only [Fin.val_mk] at *) <;>
    first
    | rfl
    | (exfalso; omega)
    | (congr 1; ext; simp only [Fin.val_mk]; omega)
    | (congr 2; ext; simp only [Fin.val_mk]; omega)

private theorem star_bvec_dotProduct {m : ℕ} (i : Fin m) (v : Fin m → ℂ) : star (bvec i) ⬝ᵥ v = v i := by
  have h : star (bvec i : Fin m → ℂ) = bvec i := by
    ext j
    simp only [bvec, Pi.star_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [h, bvec, single_dotProduct, one_mul]

private theorem Hpk_mulVec_apply_wI_zero (k r' : ℕ) (hk : 1 ≤ k) (x : Fin (2 * r' + k + 1) → ℂ) :
    (Hpk k r' *ᵥ x) (wI k r' 0) = x (wI k r' 0) := by
  rw [Hpk_mulVec_apply_eq_ite, if_neg (by simp only [wI, Fin.val_zero, Fin.val_mk]; omega),
    if_neg (by simp only [wI, Fin.val_zero, Fin.val_mk]; omega)]

private theorem Hpk_mulVec_apply_wI_last (k r' : ℕ) (x : Fin (2 * r' + k + 1) → ℂ) :
    (Hpk k r' *ᵥ x) (wI k r' (Fin.last k)) = -x (wI k r' (Fin.last k)) := by
  rw [Hpk_mulVec_apply_eq_ite, if_neg (by simp only [wI, Fin.val_last, Fin.val_mk]; omega),
    if_pos (by simp only [wI, Fin.val_last, Fin.val_mk])]

private theorem star_phiV_dotProduct_Hpk_mulVec_eq_aF (k r' : ℕ) (hk : 1 ≤ k) (x : Fin (2 * r' + k + 1) → ℂ) (t : Fin (r' + 1)) :
    star (phiV k r' t) ⬝ᵥ (Hpk k r' *ᵥ x) = aF k r' x t := by
  have htl := t.isLt
  unfold phiV aF
  by_cases ht : (t : ℕ) < r'
  · rw [dif_pos ht, dif_pos ht, star_bvec_dotProduct]
    show (Hpk k r' *ᵥ x) ⟨2 * r' + k - (t : ℕ), by omega⟩ = _
    rw [Hpk_mulVec_apply_eq_ite, if_pos (by simp only [Fin.val_mk]; omega)]
    congr 1
    ext
    simp only [eI, Fin.val_mk]
    omega
  · rw [dif_neg ht, dif_neg ht]
    have e1 := Hpk_mulVec_apply_wI_zero k r' hk x
    have e2 := Hpk_mulVec_apply_wI_last k r' x
    have hc : star (((Real.sqrt 2)⁻¹ : ℂ)) = cc := by
      unfold cc
      rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
    simp only [epsV, star_smul, star_add, smul_dotProduct, add_dotProduct, star_bvec_dotProduct, e1, e2,
      smul_eq_mul]
    rw [hc, sub_eq_add_neg]

theorem heis_lift (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (t : Fin (r' + 1)) :
    heis0 k r' x *ᵥ liftVec k 1 r' (phiV k r' t) = liftVec k 1 r' (phiV k r' t) - star (aF k r' x.1 t) • e0 k r' := by
  rw [heis0, heisG_mulVec_eq, sum_herm_bvec_mul_eq_herm, sum_herm_bvec_mul_eq_herm]
  have hE : herm (Hpk k (1 + r')) (liftVec k 1 r' (phiV k r' t)) (e0 k r') = 0 := by
    rw [herm, Hpk_one_add_mulVec_liftVec]
    exact d_e_l k r' _
  have hA : herm (Hpk k (1 + r')) (liftVec k 1 r' (phiV k r' t)) (liftVec k 1 r' x.1) =
      star (aF k r' x.1 t) := by
    rw [herm, Hpk_one_add_mulVec_liftVec, star_liftVec_dotProduct_liftVec, ← herm, herm_symm, herm]
    congr 1
    exact star_phiV_dotProduct_Hpk_mulVec_eq_aF k r' hk x.1 t
  rw [hE, hA, zero_smul, add_zero]

theorem sum_lt_split (N m : ℕ) (hm : m ≤ N) (f : ℕ → ℂ) :
    ∑ j ∈ Finset.range N, f j = ∑ j ∈ Finset.range m, f j + ∑ j ∈ Finset.range N, (if m ≤ j then f j else 0) := by
  rw [← Finset.sum_range_add_sum_Ico f hm, ← Finset.sum_filter]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext j
  simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
  omega

theorem final_alg (N m : ℕ) (hm : m ≤ N) (A A' : ℕ → ℂ) (Uu b : ℂ) :
    let x : ℕ → ℂ := fun j => A' j - b * A j
    (1 + (∑ j ∈ Finset.range N, (star (A j) * A j + star (A' j) * A' j) + Uu + b * star b) -
        ∑ j ∈ Finset.range m, star (x j) * x j) * (1 + ∑ j ∈ Finset.range m, star (A j) * A j) +
      (∑ j ∈ Finset.range m, star (x j) * A j) * (∑ j ∈ Finset.range m, star (A j) * x j) =
    (1 + ∑ j ∈ Finset.range m, star (A j) * A j) * ((1 + ∑ j ∈ Finset.range N, star (A j) * A j) + Uu +
        ∑ j ∈ Finset.range N, (if m ≤ j then star (A' j) * A' j else 0)) +
      (b + ∑ j ∈ Finset.range m, A' j * star (A j)) * star (b + ∑ j ∈ Finset.range m, A' j * star (A j)) := by
  intro x
  have hx1 : ∑ j ∈ Finset.range m, star (x j) * x j = ∑ j ∈ Finset.range m, star (A' j) * A' j -
      b * ∑ j ∈ Finset.range m, star (A' j) * A j - star b * ∑ j ∈ Finset.range m, star (A j) * A' j +
      b * star b * ∑ j ∈ Finset.range m, star (A j) * A j := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [x, star_sub, star_mul']
    ring
  have hx2 : ∑ j ∈ Finset.range m, star (x j) * A j = ∑ j ∈ Finset.range m, star (A' j) * A j -
      star b * ∑ j ∈ Finset.range m, star (A j) * A j := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [x, star_sub, star_mul']
    ring
  have hx3 : ∑ j ∈ Finset.range m, star (A j) * x j = ∑ j ∈ Finset.range m, star (A j) * A' j -
      b * ∑ j ∈ Finset.range m, star (A j) * A j := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [x]
    ring
  have hq : ∑ j ∈ Finset.range m, A' j * star (A j) = ∑ j ∈ Finset.range m, star (A j) * A' j :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hs : star (b + ∑ j ∈ Finset.range m, star (A j) * A' j) =
      star b + ∑ j ∈ Finset.range m, star (A' j) * A j := by
    rw [star_add, star_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [star_mul', star_star, mul_comm]
  rw [hx1, hx2, hx3, hq, hs, Finset.sum_add_distrib, sum_lt_split N m hm (fun j => star (A' j) * A' j)]
  ring

theorem hmv_mid (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (v : ℕ) (h : v < 2 * r + k + 1) (h1 : r ≤ v) (h2 : v < r + k) :
    (Hpk k r *ᵥ y) ⟨v, h⟩ = y ⟨v, h⟩ := by
  rw [Hpk_mulVec_apply_eq_ite, if_neg (by simp only [Fin.val_mk]; omega), if_neg (by simp only [Fin.val_mk]; omega)]

theorem hmv_top (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (h : r + k < 2 * r + k + 1) :
    (Hpk k r *ᵥ y) ⟨r + k, h⟩ = -y ⟨r + k, h⟩ := by
  rw [Hpk_mulVec_apply_eq_ite, if_neg (by simp only [Fin.val_mk]; omega), if_pos (by simp only [Fin.val_mk])]

theorem hmv_out (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (v : ℕ) (h : v < 2 * r + k + 1) (hv : v < r ∨ r + k < v) :
    (Hpk k r *ᵥ y) ⟨v, h⟩ = y ⟨2 * r + k - v, by omega⟩ := by
  rw [Hpk_mulVec_apply_eq_ite, if_pos (by simp only [Fin.val_mk]; omega)]

def ix (k r' : ℕ) : Fin (r' + 1) ⊕ (Fin (r' + 1) ⊕ Fin (k - 1)) → Fin (2 * r' + k + 1)
  | Sum.inl t => ⟨t.val, by omega⟩
  | Sum.inr (Sum.inl t) => ⟨2 * r' + k - t.val, by omega⟩
  | Sum.inr (Sum.inr i) => ⟨r' + i.val + 1, by omega⟩

theorem ix_inj (k r' : ℕ) (hk : 1 ≤ k) : Function.Injective (ix k r') := by
  intro a b h
  rcases a with t | t | i <;> rcases b with s | s | j <;>
    simp only [ix, Fin.mk.injEq] at h <;>
    simp only [Sum.inl.injEq, Sum.inr.injEq, Fin.ext_iff, reduceCtorEq] <;> omega

theorem ix_bij (k r' : ℕ) (hk : 1 ≤ k) : Function.Bijective (ix k r') := (Fintype.bijective_iff_injective_and_card _).mpr
  ⟨ix_inj k r' hk, by simp only [Fintype.card_sum, Fintype.card_fin]; omega⟩

theorem rankOne_base_weight_eq_cmTheta (k r' : ℕ) (t : Fin (r' + 1)) (ht : ¬ t.val < r') (h : t.val < 2 * r' + k + 1) :
    (⟨t.val, h⟩ : Fin (2 * r' + k + 1)) = wI k r' 0 := Fin.ext (by simp only [wI, Fin.val_zero, Fin.val_mk]; omega)

theorem wk_eq (k r' : ℕ) (t : Fin (r' + 1)) (ht : ¬ t.val < r') (h : 2 * r' + k - t.val < 2 * r' + k + 1) :
    (⟨2 * r' + k - t.val, h⟩ : Fin (2 * r' + k + 1)) = wI k r' (Fin.last k) := Fin.ext (by simp only [wI, Fin.val_last, Fin.val_mk]; omega)

private theorem star_cc_mul_cc : star cc * cc = (1 / 2 : ℂ) := by
  unfold cc
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem pars1 (k r' : ℕ) (hk : 1 ≤ k) (y : Fin (2 * r' + k + 1) → ℂ) :
    star y ⬝ᵥ y = ∑ t : Fin (r' + 1), (star (aF k r' y t) * aF k r' y t + star (aF' k r' y t) * aF' k r' y t) +
      ∑ i : Fin (k - 1), star (y (ix k r' (Sum.inr (Sum.inr i)))) * y (ix k r' (Sum.inr (Sum.inr i))) := by
  have hcc := star_cc_mul_cc
  have hb := ix_bij k r' hk
  rw [dotProduct, ← (Equiv.ofBijective _ hb).sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type, ← add_assoc,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have htl := t.isLt
  simp only [Equiv.ofBijective_apply, Pi.star_apply]
  unfold aF aF'
  by_cases ht : (t : ℕ) < r'
  · rw [dif_pos ht, dif_pos ht]
    rfl
  · rw [dif_neg ht, dif_neg ht]
    have h0 : ix k r' (Sum.inl t) = wI k r' 0 := rankOne_base_weight_eq_cmTheta k r' t ht _
    have h1 : ix k r' (Sum.inr (Sum.inl t)) = wI k r' (Fin.last k) := wk_eq k r' t ht _
    rw [h0, h1]
    simp only [star_mul', star_sub, star_add]
    linear_combination (-(2 * star (y (wI k r' 0)) * y (wI k r' 0) +
      2 * star (y (wI k r' (Fin.last k))) * y (wI k r' (Fin.last k)))) * hcc

theorem pars2 (k r' : ℕ) (hk : 1 ≤ k) (y : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k r') y y = ∑ t : Fin (r' + 1), (star (aF k r' y t) * aF' k r' y t + star (aF' k r' y t) * aF k r' y t) +
      ∑ i : Fin (k - 1), star (y (ix k r' (Sum.inr (Sum.inr i)))) * y (ix k r' (Sum.inr (Sum.inr i))) := by
  have hcc := star_cc_mul_cc
  have hb := ix_bij k r' hk
  rw [herm, dotProduct, ← (Equiv.ofBijective _ hb).sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type,
    ← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have htl := t.isLt
  simp only [Equiv.ofBijective_apply, Pi.star_apply]
  unfold aF aF'
  by_cases ht : (t : ℕ) < r'
  · rw [dif_pos ht, dif_pos ht]
    have h1 : (Hpk k r' *ᵥ y) (ix k r' (Sum.inl t)) = y (ix k r' (Sum.inr (Sum.inl t))) :=
      hmv_out k r' y (t : ℕ) _ (Or.inl ht)
    have h2 : (Hpk k r' *ᵥ y) (ix k r' (Sum.inr (Sum.inl t))) = y (ix k r' (Sum.inl t)) := by
      rw [show ix k r' (Sum.inr (Sum.inl t)) = ⟨2 * r' + k - (t : ℕ), by omega⟩ from rfl,
        hmv_out k r' y _ _ (Or.inr (by omega))]
      congr 1
      ext
      show 2 * r' + k - (2 * r' + k - (t : ℕ)) = (t : ℕ)
      omega
    rw [h1, h2]
    rfl
  · rw [dif_neg ht, dif_neg ht]
    have h0 : ix k r' (Sum.inl t) = wI k r' 0 := rankOne_base_weight_eq_cmTheta k r' t ht _
    have h1 : ix k r' (Sum.inr (Sum.inl t)) = wI k r' (Fin.last k) := wk_eq k r' t ht _
    rw [h0, h1, Hpk_mulVec_apply_wI_zero k r' hk y, Hpk_mulVec_apply_wI_last k r' y]
    simp only [star_mul', star_sub, star_add]
    linear_combination (-(2 * star (y (wI k r' 0)) * y (wI k r' 0) -
      2 * star (y (wI k r' (Fin.last k))) * y (wI k r' (Fin.last k)))) * hcc
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.isLt
  simp only [Equiv.ofBijective_apply, Pi.star_apply]
  congr 1
  exact hmv_mid k r' y (r' + (i : ℕ) + 1) (by omega) (by omega) (by omega)

end FormulaFAux

end ReciprocityTheory.ChartRestriction.DS.Xi
