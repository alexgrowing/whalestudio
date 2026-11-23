import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptGen

noncomputable section

namespace PIW.MassDataColumns

open Matrix Formalism.FourierDecayAlt.S3
open scoped Matrix

variable {K : Type} [Field K] (O : Subring K) {r k : ℕ}

theorem dlH_dlH' (s : Idx r k) : dlH (dlH s) = s := by
  rcases s with a | ((i | u) | c) <;> simp [dlH]

theorem nMat_col_w (o : Idx r k → Fin k → K) (l : Idx r k → K) (g : K) (i : Fin k) :
    nMat o l g *ᵥ Pi.single (wI i) 1 = coefv o l g i := by
  ext t
  rw [Matrix.mulVec_single_one]
  rfl

theorem nMat_col_frame (o : Idx r k → Fin k → K) (l : Idx r k → K) (g : K) (s : Idx r k) (hs : ¬ IsW s) :
    nMat o l g *ᵥ Pi.single s 1 = 0 := by
  ext t
  rw [Matrix.mulVec_single_one]
  rcases s with a | ((i | u) | b)
  · rfl
  · exact absurd ⟨i, rfl⟩ hs
  · rfl
  · rfl

theorem one_sub_mul_one_add (N : Matrix (Idx r k) (Idx r k) K) (hN : N * N = 0) : (1 - N) * (1 + N) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, hN, add_zero, add_sub_cancel_right]

theorem one_add_mul_one_sub (N : Matrix (Idx r k) (Idx r k) K) (hN : N * N = 0) : (1 + N) * (1 - N) = 1 := by
  rw [add_mul, one_mul, mul_sub, mul_one, hN, sub_zero, sub_add_cancel]

theorem intO_nMat (o : Idx r k → Fin k → K) (l : Idx r k → K) (g : K) (hg : g ∈ O) (ho : ∀ s i, o s i ∈ O)
    (hl : ∀ s, ¬ IsW s → (l s)⁻¹ ∈ O) : IntO O (nMat o l g) := by
  intro t s
  unfold nMat ofCols
  rcases s with a | ((i | u) | b)
  · exact O.zero_mem
  · show coefv o l g i t ∈ O
    unfold coefv
    split_ifs with ht
    · exact O.zero_mem
    · have hW : ¬ IsW (dlH t) := by
        rintro ⟨j, hj⟩
        apply ht
        rcases t with a' | ((i' | u') | c') <;> simp [dlH] at hj
        exact ⟨i', rfl⟩
      exact O.mul_mem (O.mul_mem hg (ho _ _)) (hl _ hW)
  · exact O.zero_mem
  · exact O.zero_mem

private theorem intO_mul' {A B : Matrix (Idx r k) (Idx r k) K} (hA : IntO O A) (hB : IntO O B) :
    IntO O (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  exact O.sum_mem (fun x _ => O.mul_mem (hA i x) (hB x j))

private theorem intO_one_sub {N : Matrix (Idx r k) (Idx r k) K} (hN : IntO O N) : IntO O (1 - N) := by
  intro i j
  rw [Matrix.sub_apply]
  refine O.sub_mem ?_ (hN i j)
  rw [Matrix.one_apply]
  split_ifs
  exacts [O.one_mem, O.zero_mem]

private theorem intO_one_add {N : Matrix (Idx r k) (Idx r k) K} (hN : IntO O N) : IntO O (1 + N) := by
  intro i j
  rw [Matrix.add_apply]
  refine O.add_mem ?_ (hN i j)
  rw [Matrix.one_apply]
  split_ifs
  exacts [O.one_mem, O.zero_mem]

private theorem nMat_mul_self_eq_zero (o : Idx r k → Fin k → K) (l : Idx r k → K) (g : K) :
    nMat o l g * nMat o l g = 0 := by
  ext t s
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : IsW x
  · have e : nMat o l g x s = 0 := by
      unfold nMat ofCols
      rcases s with a | ((i | u) | b)
      · rfl
      · show coefv o l g i x = 0
        unfold coefv
        rw [if_pos hx]
      · rfl
      · rfl
    rw [e, mul_zero]
  · have e := congrFun (nMat_col_frame o l g x hx) t
    rw [Matrix.mulVec_single_one] at e
    have e' : nMat o l g t x = 0 := e
    rw [e', zero_mul]

theorem adapted_gen (P : GL (Idx r k) K) (c : Idx r k → Idx r k → K) (y : Fin k → Idx r k → K)
    (a : Idx r k → Idx r k → K) (l : Idx r k → K) (o : Idx r k → Fin k → K) (g : K)
    (hac : ∀ s t, ¬ IsW s → ¬ IsW t → a s ⬝ᵥ c t = if t = dlH s then l s else 0)
    (hay : ∀ s i, ¬ IsW s → a s ⬝ᵥ y i = g * o s i)
    (hl0 : ∀ s, ¬ IsW s → l s ≠ 0) (hlinv : ∀ s, ¬ IsW s → (l s)⁻¹ ∈ O)
    (ho : ∀ s i, o s i ∈ O) (hg : g ∈ O)
    (hC : IntO O (((P⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) * ofCols (colv c y)))
    (u : K) (huO : u ∈ O)
    (hdet : (((P⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) * ofCols (colv c y)).det * u = 1) :
    ∃ Q : GL (Idx r k) K,
      (∀ s, ¬ IsW s → ((Q⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) *ᵥ c s = Pi.single s 1) ∧
      (∀ s, ¬ IsW s → (Q : Matrix (Idx r k) (Idx r k) K)ᵀ *ᵥ a s = l s • Pi.single (dlH s) 1) ∧
      IntO O (((P⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) * (Q : Matrix (Idx r k) (Idx r k) K)) ∧
      IntO O (((Q⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) * (P : Matrix (Idx r k) (Idx r k) K)) ∧
      ∀ i, ∃ cc : Idx r k → O, (Q : Matrix (Idx r k) (Idx r k) K) *ᵥ Pi.single (wI i) 1 - y i =
        g • ((Q : Matrix (Idx r k) (Idx r k) K) *ᵥ fun s => (cc s : K)) := by
  classical
  have hPP : ((P : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) * (((P⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K)) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPu : IsUnit (((P : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K)).det := Matrix.isUnits_det_units P
  have hN2 : (nMat o l g : Matrix (Idx r k) (Idx r k) K) * (nMat o l g : Matrix (Idx r k) (Idx r k) K) = 0 := nMat_mul_self_eq_zero o l g
  have hCu : IsUnit ((((P⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K)) * (ofCols (colv c y) : Matrix (Idx r k) (Idx r k) K)).det := isUnit_iff_exists_inv.2 ⟨u, hdet⟩
  have hBeq : (ofCols (colv c y) : Matrix (Idx r k) (Idx r k) K) = ((P : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) * ((((P⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K)) * (ofCols (colv c y) : Matrix (Idx r k) (Idx r k) K)) := by rw [← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hBu : IsUnit ((ofCols (colv c y) : Matrix (Idx r k) (Idx r k) K)).det := by
    rw [hBeq, Matrix.det_mul]
    exact hPu.mul hCu
  have h1N : IsUnit (1 - (nMat o l g : Matrix (Idx r k) (Idx r k) K)).det := by
    have e := congrArg Matrix.det (one_sub_mul_one_add _ hN2)
    rw [Matrix.det_mul, Matrix.det_one] at e
    exact isUnit_iff_exists_inv.2 ⟨_, e⟩
  have hQu : IsUnit ((ofCols (colv c y) : Matrix (Idx r k) (Idx r k) K) * (1 - (nMat o l g : Matrix (Idx r k) (Idx r k) K))).det := by
    rw [Matrix.det_mul]
    exact hBu.mul h1N
  have hdlW : ∀ s : Idx r k, ¬ IsW s → ¬ IsW (dlH s) := by
    intro s hs ⟨j, hj⟩
    apply hs
    rcases s with a' | ((i' | u') | c') <;> simp [dlH] at hj
    exact ⟨i', rfl⟩
  have hcolv : ∀ x, ¬ IsW x → colv c y x = c x := by
    intro x hx
    rcases x with a' | ((i' | u') | c')
    · rfl
    · exact absurd ⟨i', rfl⟩ hx
    · rfl
    · rfl
  have hcol : ∀ s, ¬ IsW s → (ofCols (colv c y) : Matrix (Idx r k) (Idx r k) K) *ᵥ Pi.single s 1 = c s := by
    intro s hs
    ext t
    rw [Matrix.mulVec_single_one]
    show colv c y s t = c s t
    rw [hcolv s hs]
  have hcolW : ∀ i, (ofCols (colv c y) : Matrix (Idx r k) (Idx r k) K) *ᵥ Pi.single (wI i) 1 = y i := by
    intro i
    ext t
    rw [Matrix.mulVec_single_one]
    rfl
  have hNv : ∀ v : Idx r k → K, (∀ x, IsW x → v x = 0) → (nMat o l g : Matrix (Idx r k) (Idx r k) K) *ᵥ v = 0 := by
    intro v hv
    ext t
    rw [Matrix.mulVec, dotProduct, Pi.zero_apply]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : IsW x
    · rw [hv x hx, mul_zero]
    · have e := congrFun (nMat_col_frame o l g x hx) t
      rw [Matrix.mulVec_single_one] at e
      have e' : nMat o l g t x = 0 := e
      rw [e', zero_mul]
  have hvB : ∀ (v : Idx r k → K) (x : Idx r k), ¬ IsW x → (v ᵥ* (ofCols (colv c y) : Matrix (Idx r k) (Idx r k) K)) x = v ⬝ᵥ c x := by
    intro v x hx
    rw [← hcolv x hx]
    rfl
  have hdotB : ∀ s, ¬ IsW s → ∀ v : Idx r k → K, (∀ x, IsW x → v x = 0) →
      a s ⬝ᵥ ((ofCols (colv c y) : Matrix (Idx r k) (Idx r k) K) *ᵥ v) = l s * v (dlH s) := by
    intro s hs v hv
    rw [Matrix.dotProduct_mulVec, dotProduct, Finset.sum_eq_single (dlH s)]
    · rw [hvB _ _ (hdlW s hs), hac s _ hs (hdlW s hs), if_pos rfl]
    · intro x _ hx
      by_cases hW : IsW x
      · rw [hv x hW, mul_zero]
      · rw [hvB _ _ hW, hac s x hs hW, if_neg hx, zero_mul]
    · simp
  let Q : GL (Idx r k) K := Matrix.nonsingInvUnit ((ofCols (colv c y) : Matrix (Idx r k) (Idx r k) K) * (1 - (nMat o l g : Matrix (Idx r k) (Idx r k) K))) hQu
  have hQ : (Q : Matrix (Idx r k) (Idx r k) K) = (ofCols (colv c y) : Matrix (Idx r k) (Idx r k) K) * (1 - (nMat o l g : Matrix (Idx r k) (Idx r k) K)) := rfl
  have hQs : ∀ s, ¬ IsW s → (Q : Matrix (Idx r k) (Idx r k) K) *ᵥ Pi.single s 1 = c s := by
    intro s hs
    rw [hQ, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, nMat_col_frame o l g s hs,
      sub_zero, hcol s hs]
  refine ⟨Q, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [← hQs s hs, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  · intro s hs
    ext t
    rw [Matrix.mulVec_transpose]
    have hvt : ∀ (M : Matrix (Idx r k) (Idx r k) K) (v : Idx r k → K) (t : Idx r k),
        (v ᵥ* M) t = v ⬝ᵥ (M *ᵥ Pi.single t 1) := by
      intro M v t
      rw [Matrix.mulVec_single_one]
      rfl
    rw [hvt]
    by_cases ht : IsW t
    · obtain ⟨i, rfl⟩ := ht
      have hW0 : ∀ x, IsW x → coefv o l g i x = 0 := by
        intro x hx
        unfold coefv
        rw [if_pos hx]
      rw [hQ, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, hcolW,
        nMat_col_w, dotProduct_sub, hay s i hs, hdotB s hs _ hW0]
      have hne : (Sum.inr (Sum.inl (Sum.inl i)) : Idx r k) ≠ dlH s := fun h => hdlW s hs ⟨i, h.symm⟩
      rw [Pi.smul_apply, Pi.single_eq_of_ne hne, smul_zero]
      unfold coefv
      rw [if_neg (hdlW s hs), dlH_dlH', mul_comm (l s), mul_assoc, inv_mul_cancel₀ (hl0 s hs), mul_one, sub_self]
    · rw [hQs t ht, hac s t hs ht, Pi.smul_apply, Pi.single_apply]
      split_ifs <;> simp
  · rw [hQ, ← Matrix.mul_assoc]
    exact intO_mul' O hC (intO_one_sub O (intO_nMat O o l g hg ho hlinv))
  · have hinvN : (1 - (nMat o l g : Matrix (Idx r k) (Idx r k) K))⁻¹ = 1 + (nMat o l g : Matrix (Idx r k) (Idx r k) K) := Matrix.inv_eq_right_inv (one_sub_mul_one_add _ hN2)
    let C' : Matrix (Idx r k) (Idx r k) O := fun i j => ⟨((((P⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K)) * (ofCols (colv c y) : Matrix (Idx r k) (Idx r k) K)) i j, hC i j⟩
    have hCC : C'.map O.subtype = (((P⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K)) * (ofCols (colv c y) : Matrix (Idx r k) (Idx r k) K) := by
      ext i j
      rfl
    have hadj : ∀ i j, ((((P⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K)) * (ofCols (colv c y) : Matrix (Idx r k) (Idx r k) K)).adjugate i j ∈ O := by
      intro i j
      have e := RingHom.map_adjugate O.subtype C'
      rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hCC] at e
      rw [← e]
      exact (C'.adjugate i j).2
    have hCinv : IntO O (((((P⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K)) * (ofCols (colv c y) : Matrix (Idx r k) (Idx r k) K))⁻¹) := by
      rw [Matrix.inv_eq_left_inv (B := u • ((((P⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K)) * (ofCols (colv c y) : Matrix (Idx r k) (Idx r k) K)).adjugate) (by
        rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm u, hdet, one_smul])]
      intro i j
      rw [Matrix.smul_apply, smul_eq_mul]
      exact O.mul_mem huO (hadj i j)
    rw [Matrix.coe_units_inv, hQ, Matrix.mul_inv_rev, hinvN, hBeq, Matrix.mul_inv_rev, Matrix.mul_assoc,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu, Matrix.mul_one]
    exact intO_mul' O (intO_one_add O (intO_nMat O o l g hg ho hlinv)) hCinv
  · intro i
    have hvO : ∀ t, (fun t : Idx r k => if IsW t then (0 : K) else o (dlH t) i * (l (dlH t))⁻¹) t ∈ O := by
      intro t
      show (if IsW t then (0 : K) else o (dlH t) i * (l (dlH t))⁻¹) ∈ O
      split_ifs with ht
      · exact O.zero_mem
      · exact O.mul_mem (ho _ _) (hlinv _ (hdlW t ht))
    refine ⟨fun t => ⟨-((fun t : Idx r k => if IsW t then (0 : K) else o (dlH t) i * (l (dlH t))⁻¹) t), O.neg_mem (hvO t)⟩, ?_⟩
    have hcoef : coefv o l g i = g • (fun t : Idx r k => if IsW t then (0 : K) else o (dlH t) i * (l (dlH t))⁻¹) := by
      funext t
      unfold coefv
      simp only [Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp [mul_assoc]
    have hvW : ∀ x, IsW x → (fun t : Idx r k => if IsW t then (0 : K) else o (dlH t) i * (l (dlH t))⁻¹) x = 0 := by
      intro x hx
      show (if IsW x then (0 : K) else o (dlH x) i * (l (dlH x))⁻¹) = 0
      rw [if_pos hx]
    have hQv : (Q : Matrix (Idx r k) (Idx r k) K) *ᵥ (fun t : Idx r k => if IsW t then (0 : K) else o (dlH t) i * (l (dlH t))⁻¹) = (ofCols (colv c y) : Matrix (Idx r k) (Idx r k) K) *ᵥ (fun t : Idx r k => if IsW t then (0 : K) else o (dlH t) i * (l (dlH t))⁻¹) := by
      rw [hQ, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hNv _ hvW, sub_zero]
    change _ = g • ((Q : Matrix (Idx r k) (Idx r k) K) *ᵥ (-(fun t : Idx r k => if IsW t then (0 : K) else o (dlH t) i * (l (dlH t))⁻¹)))
    rw [Matrix.mulVec_neg, hQv, hQ, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_sub, hcolW, nMat_col_w, hcoef, Matrix.mulVec_smul, smul_neg]
    abel

end PIW.MassDataColumns
