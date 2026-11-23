import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InvSqrtTwoMulSelf

noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

theorem Iic_zero (n : ℕ) : Finset.Iic (0 : Fin (n + 1)) = {0} := by
  ext a
  simp [Fin.le_zero_iff]

section Lv
variable {k r' : ℕ}

def su (a : Fin (r' + 1)) : Fin (1 + r' + 1) := ⟨a.val + 1, by omega⟩

theorem su_val (a : Fin (r' + 1)) : (su a).val = a.val + 1 := rfl

theorem exists_su (a : Fin (1 + r' + 1)) (ha : a.val ≠ 0) : ∃ b : Fin (r' + 1), a = su b := by
  refine ⟨⟨a.val - 1, by have := a.2; omega⟩, Fin.ext ?_⟩
  show a.val = (a.val - 1) + 1
  omega

theorem prod_su {M : Type} [CommMonoid M] (f : Fin (1 + r' + 1) → M) :
    ∏ l, f l = f 0 * ∏ a : Fin (r' + 1), f (su a) := by
  rw [Fin.prod_univ_succ]
  congr 1
  exact (Fintype.prod_equiv (finCongr (by omega : r' + 1 = 1 + r')) (fun a => f (su a))
    (fun b => f b.succ) fun a => congrArg f (Fin.ext (by simp [su]))).symm

theorem sum_su {M : Type} [AddCommMonoid M] (f : Fin (1 + r' + 1) → M) :
    ∑ l, f l = f 0 + ∑ a : Fin (r' + 1), f (su a) := by
  rw [Fin.sum_univ_succ]
  congr 1
  exact (Fintype.sum_equiv (finCongr (by omega : r' + 1 = 1 + r')) (fun a => f (su a))
    (fun b => f b.succ) fun a => congrArg f (Fin.ext (by simp [su]))).symm

theorem lv_add (v w : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' (v + w) = liftVec k 1 r' v + liftVec k 1 r' w := by
  ext p
  simp only [liftVec, Pi.add_apply]
  split_ifs <;> simp

theorem lv_smul (c : ℂ) (v : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' (c • v) = c • liftVec k 1 r' v := by
  ext p
  simp only [liftVec, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem lv_sum {ι : Type} (s : Finset ι) (f : ι → Fin (2 * r' + k + 1) → ℂ) :
    liftVec k 1 r' (∑ i ∈ s, f i) = ∑ i ∈ s, liftVec k 1 r' (f i) := by
  have e : liftVec k 1 r' (∑ i ∈ s, f i) =
      (AddMonoidHom.mk' (liftVec k 1 r') fun v w => lv_add v w) (∑ i ∈ s, f i) := rfl
  rw [e, map_sum]
  rfl

theorem phi_lift (a : Fin (r' + 1)) : liftVec k 1 r' (phiV k r' a) = phiV k (1 + r') (su a) := by
  unfold phiV
  by_cases h : a.val < r'
  · have h' : (su a).val < 1 + r' := by rw [su_val]; omega
    rw [dif_pos h, dif_pos h', ← bvec_lv]
    congr 1
    ext
    simp only [sh, esI, su_val, Fin.val_mk]
    omega
  · have h' : ¬ (su a).val < 1 + r' := by rw [su_val]; omega
    rw [dif_neg h, dif_neg h']
    unfold epsV
    have e0 : sh (wI k r' 0) = wI k (1 + r') 0 := by
      ext
      simp only [sh, wI, Fin.val_mk]
      omega
    have e1 : sh (wI k r' (Fin.last k)) = wI k (1 + r') (Fin.last k) := by
      ext
      simp only [sh, wI, Fin.val_mk]
      omega
    rw [lv_smul, lv_add, ← bvec_lv, ← bvec_lv, e0, e1]

theorem besselPhi_eq_reindexConj_rootCoords : phiV k (1 + r') 0 = bvec ⟨2 * (1 + r') + k, by omega⟩ := by
  unfold phiV
  rw [dif_pos (by simp only [Fin.val_zero]; omega)]
  congr 1

theorem levelEmbedding_fixes_firstVector (g : Mat k r') : ιLev k 1 r' g *ᵥ phiV k (1 + r') 0 = phiV k (1 + r') 0 := by
  rw [besselPhi_eq_reindexConj_rootCoords]
  exact io_bvec_out g _ (Or.inr rfl)

theorem io_phi_su (g : Mat k r') (a : Fin (r' + 1)) :
    ιLev k 1 r' g *ᵥ phiV k (1 + r') (su a) = liftVec k 1 r' (g *ᵥ phiV k r' a) := by
  rw [← phi_lift, io_lv]

def tt (τ : Matrix (Fin (r' + 1)) (Fin (r' + 1)) ℂ) : Matrix (Fin (1 + r' + 1)) (Fin (1 + r' + 1)) ℂ := fun i j =>
  if i.val = 0 then (if j.val = 0 then 1 else 0)
  else if hj : j.val = 0 then 0 else τ ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩

variable (τ : Matrix (Fin (r' + 1)) (Fin (r' + 1)) ℂ)

theorem tt_su (a b : Fin (r' + 1)) : tt τ (su b) (su a) = τ b a := by
  unfold tt
  rw [if_neg (by simp [su]), dif_neg (by simp [su])]
  congr 1 <;> ext <;> simp [su]

theorem tt_00 : tt τ 0 0 = 1 := by
  simp [tt]

theorem triangularCoeff_firstColumn_zero (b : Fin (1 + r' + 1)) (hb : b.val ≠ 0) : tt τ b 0 = 0 := by
  simp [tt, hb]

theorem tt_0su (a : Fin (r' + 1)) : tt τ 0 (su a) = 0 := by
  simp [tt, su]

theorem tt_tri (hτ : τ.BlockTriangular id) : (tt τ).BlockTriangular id := by
  intro i j hij
  simp only [id] at hij
  rw [Fin.lt_iff_val_lt_val] at hij
  unfold tt
  by_cases hi : i.val = 0
  · omega
  · rw [if_neg hi]
    by_cases hj : j.val = 0
    · rw [dif_pos hj]
    · rw [dif_neg hj]
      apply hτ
      simp only [id, Fin.mk_lt_mk]
      omega

theorem tt_rep (m κ : Mat k r') (hrep : ∀ a, m *ᵥ phiV k r' a = ∑ b, τ b a • (κ *ᵥ phiV k r' b))
    (a : Fin (1 + r' + 1)) :
    ιLev k 1 r' m *ᵥ phiV k (1 + r') a = ∑ b, tt τ b a • (ιLev k 1 r' κ *ᵥ phiV k (1 + r') b) := by
  by_cases ha : a.val = 0
  · have ha0 : a = 0 := Fin.ext ha
    subst ha0
    rw [levelEmbedding_fixes_firstVector, sum_su, tt_00, levelEmbedding_fixes_firstVector, one_smul]
    rw [Finset.sum_eq_zero fun b _ => by rw [triangularCoeff_firstColumn_zero τ (su b) (by simp [su]), zero_smul], add_zero]
  · obtain ⟨a', rfl⟩ := exists_su a ha
    rw [io_phi_su, hrep a', lv_sum, sum_su, tt_0su, zero_smul, zero_add]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [tt_su, io_phi_su, lv_smul]

def suE : Fin (r' + 1) ↪ Fin (1 + r' + 1) :=
  ⟨su, fun a b h => Fin.ext (by have := congrArg Fin.val h; simp only [su_val] at this; omega)⟩

theorem Iic_su (a : Fin (r' + 1)) : Finset.Iic (su a) = insert 0 ((Finset.Iic a).map suE) := by
  ext l
  simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_map]
  constructor
  · intro hl
    by_cases h0 : l.val = 0
    · exact Or.inl (Fin.ext h0)
    · obtain ⟨b, rfl⟩ := exists_su l h0
      refine Or.inr ⟨b, ?_, rfl⟩
      rw [Fin.le_iff_val_le_val] at hl ⊢
      rw [su_val, su_val] at hl
      omega
  · rintro (rfl | ⟨b, hb, rfl⟩)
    · exact Fin.zero_le _
    · show su b ≤ su a
      rw [Fin.le_iff_val_le_val] at hb ⊢
      rw [su_val, su_val]
      omega

theorem tt_prod0 : ∏ j ∈ Finset.Iic (0 : Fin (1 + r' + 1)), ‖tt τ j j‖ ^ 2 = 1 := by
  rw [Iic_zero, Finset.prod_singleton, tt_00]
  simp

theorem tt_prodS (a : Fin (r' + 1)) :
    ∏ j ∈ Finset.Iic (su a), ‖tt τ j j‖ ^ 2 = ∏ j ∈ Finset.Iic a, ‖τ j j‖ ^ 2 := by
  rw [Iic_su, Finset.prod_insert, Finset.prod_map, tt_00]
  · rw [norm_one, one_pow, one_mul]
    refine Finset.prod_congr rfl fun x _ => ?_
    show ‖tt τ (su x) (su x)‖ ^ 2 = _
    rw [tt_su]
  · simp only [Finset.mem_map, not_exists, not_and]
    intro b _ h
    have h' := congrArg Fin.val h
    change (su b).val = (0 : Fin (1 + r' + 1)).val at h'
    rw [su_val] at h'
    simp at h'

theorem ga_lev (x : Mat k (1 + r')) (m κ : Mat k r') (hτ : τ.BlockTriangular id)
    (hrep : ∀ a, m *ᵥ phiV k r' a = ∑ b, τ b a • (κ *ᵥ phiV k r' b)) (l : Fin (1 + r' + 1)) :
    Ga k (1 + r') l (fun a => (x * ιLev k 1 r' m) *ᵥ phiV k (1 + r') a) =
      (∏ j ∈ Finset.Iic l, ‖tt τ j j‖ ^ 2) * Ga k (1 + r') l (fun a => (x * ιLev k 1 r' κ) *ᵥ phiV k (1 + r') a) := by
  have e : (fun a => (x * ιLev k 1 r' m) *ᵥ phiV k (1 + r') a) =
      fun a => ∑ b, tt τ b a • ((x * ιLev k 1 r' κ) *ᵥ phiV k (1 + r') b) := by
    funext a
    rw [← Matrix.mulVec_mulVec, tt_rep τ m κ hrep a, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  rw [e, ga_tri k (1 + r') _ (tt τ) (tt_tri τ hτ) l]

theorem levelDeterminant_of_triangular_change (x : Mat k (1 + r')) (m κ : Mat k r') (hτ : τ.BlockTriangular id)
    (hrep : ∀ a, m *ᵥ phiV k r' a = ∑ b, τ b a • (κ *ᵥ phiV k r' b)) :
    Del k (1 + r') 0 (x * ιLev k 1 r' m) = Del k (1 + r') 0 (x * ιLev k 1 r' κ) := by
  unfold Del
  rw [ga_lev τ x m κ hτ hrep 0, tt_prod0, one_mul]

theorem del_levS (x : Mat k (1 + r')) (m κ : Mat k r') (hτ : τ.BlockTriangular id)
    (hrep : ∀ a, m *ᵥ phiV k r' a = ∑ b, τ b a • (κ *ᵥ phiV k r' b))
    (hprod : ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k r' l (fun a => m *ᵥ phiV k r' a)) (a : Fin (r' + 1)) :
    Del k (1 + r') (su a) (x * ιLev k 1 r' m) = Del k r' a m * Del k (1 + r') (su a) (x * ιLev k 1 r' κ) := by
  unfold Del
  rw [ga_lev τ x m κ hτ hrep (su a), tt_prodS, hprod a]
  have h0 : 0 ≤ Ga k r' a (fun b => m *ᵥ phiV k r' b) := by
    rw [← hprod a]
    exact Finset.prod_nonneg fun j _ => by positivity
  exact Real.sqrt_mul h0 _

theorem del_conj (hHC : HeisConjLev) (κ : Mat k r') (hκG : κ ∈ GV k r') (hκU : κᴴ * κ = 1) (X : HPar k r')
    (l : Fin (1 + r' + 1)) :
    Del k (1 + r') l (heis0 k r' X * ιLev k 1 r' κ) = Del k (1 + r') l (heis0 k r' (κᴴ *ᵥ X.1, X.2)) := by
  have hκU' : κ * κᴴ = 1 := by
    rw [← Matrix.inv_eq_left_inv hκU]
    exact Matrix.mul_nonsing_inv κ (Matrix.isUnit_det_of_left_inverse hκU)
  have hG' : κᴴ ∈ GV k r' := by
    have hκ : κᴴ * Hpk k r' * κ = Hpk k r' := hκG
    show κᴴᴴ * Hpk k r' * κᴴ = Hpk k r'
    rw [Matrix.conjTranspose_conjTranspose]
    calc κ * Hpk k r' * κᴴ = κ * (κᴴ * Hpk k r' * κ) * κᴴ := by rw [hκ]
      _ = (κ * κᴴ) * Hpk k r' * (κ * κᴴ) := by simp only [mul_assoc]
      _ = Hpk k r' := by rw [hκU', one_mul, mul_one]
  have hinv : (ιLev k 1 r' κᴴ)⁻¹ = ιLev k 1 r' κ :=
    Matrix.inv_eq_right_inv (by rw [← io_mul, hκU, io_one])
  have hconj := hHC k r' κᴴ hG' X
  rw [hinv] at hconj
  rw [← hconj]
  have hU : (ιLev k 1 r' κᴴ)ᴴ * ιLev k 1 r' κᴴ = 1 := by
    rw [← io_conjT, Matrix.conjTranspose_conjTranspose, ← io_mul, hκU', io_one]
  unfold Del
  rw [mul_assoc]
  have e : (fun a => (ιLev k 1 r' κᴴ * (heis0 k r' X * ιLev k 1 r' κ)) *ᵥ phiV k (1 + r') a) =
      fun a => ιLev k 1 r' κᴴ *ᵥ ((heis0 k r' X * ιLev k 1 r' κ) *ᵥ phiV k (1 + r') a) := by
    funext a
    rw [Matrix.mulVec_mulVec]
  rw [e, ga_unit k (1 + r') _ hU l]

theorem rep0 (m κ : Mat k r') (hτ : τ.BlockTriangular id)
    (hrep : ∀ a, m *ᵥ phiV k r' a = ∑ b, τ b a • (κ *ᵥ phiV k r' b)) :
    m *ᵥ phiV k r' 0 = τ 0 0 • (κ *ᵥ phiV k r' 0) := by
  rw [hrep 0, Finset.sum_eq_single 0]
  · intro b _ hb
    rw [hτ (show id (0 : Fin (r' + 1)) < id b from lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hb)),
      zero_smul]
  · intro h
    exact absurd (Finset.mem_univ 0) h

theorem lev_data (hIW : IW) (hHC : HeisConjLev) (hk : 1 ≤ k) (m : Mat k r') (hm : m ∈ UH (Hpk k r')) :
    ∃ κ : Mat k r', κ ∈ GV k r' ∧ κᴴ * κ = 1 ∧ ∃ t : ℂ, m *ᵥ phiV k r' 0 = t • (κ *ᵥ phiV k r' 0) ∧
      ‖t‖ = Del k r' 0 m ∧ ∀ X : HPar k r',
        Del k (1 + r') 0 (heis0 k r' X * ιLev k 1 r' m) = Del k (1 + r') 0 (heis0 k r' (κᴴ *ᵥ X.1, X.2)) ∧
        ∀ a : Fin (r' + 1), Del k (1 + r') (su a) (heis0 k r' X * ιLev k 1 r' m) =
          Del k r' a m * Del k (1 + r') (su a) (heis0 k r' (κᴴ *ᵥ X.1, X.2)) := by
  obtain ⟨κ, hκG, hκU, τ, hτ, hrep, hprod⟩ := iw_apply (k := k) (n := r') hIW hk m hm
  refine ⟨κ, hκG, hκU, τ 0 0, rep0 τ m κ hτ hrep, ?_, fun X => ⟨?_, fun a => ?_⟩⟩
  · unfold Del
    rw [← hprod 0, Iic_zero, Finset.prod_singleton, Real.sqrt_sq (norm_nonneg _)]
  · rw [levelDeterminant_of_triangular_change τ _ m κ hτ hrep, del_conj hHC κ hκG hκU X 0]
  · rw [del_levS τ _ m κ hτ hrep hprod a, del_conj hHC κ hκG hκU X (su a)]

end Lv

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
