import Formalism.HermitianCurvature.StatementG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhaseFunctionCriticalPoints
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousInvUpper

open Matrix MeasureTheory

namespace Formalism.FourierDecayAlt.P.WeakApproximationGL

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G5

theorem tri_diag {m : ℕ} (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) (i : Fin (m + 1)) :
    triXY x y i.succ i.succ = x i := by
  simp [triXY, strictUpper]

theorem tri_lt {m : ℕ} (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) {i j : Fin (m + 2)} (h : i < j) :
    triXY x y i j = y ⟨(i, j), h⟩ := by
  simp [triXY, strictUpper, h, Matrix.diagonal_apply_ne _ h.ne]

theorem tri_gt {m : ℕ} (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) {i j : Fin (m + 2)} (h : j < i) :
    triXY x y i j = 0 := by
  simp [triXY, strictUpper, not_lt.mpr h.le, Matrix.diagonal_apply_ne _ h.ne']

abbrev FinalTheorems (m : ℕ) : Type := Fin (m + 1) ⊕ UT (m + 2)

abbrev Tgt (m : ℕ) : Type := Unit ⊕ (Fin m ⊕ (UT (m + 1) ⊕ Fin (m + 1)))

def cls {m : ℕ} (i : Fin (m + 1)) (j : Fin (m + 2)) (h : i.succ ≤ j) : FinalTheorems m :=
  if h' : i.succ = j then Sum.inl i else Sum.inr ⟨(i.succ, j), lt_of_le_of_ne h h'⟩

theorem elim_cls {m : ℕ} (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) (i : Fin (m + 1)) (j : Fin (m + 2))
    (h : i.succ ≤ j) : Sum.elim x y (cls i j h) = triXY x y i.succ j := by
  unfold cls
  split_ifs with h'
  · subst h'
    exact (tri_diag x y i).symm
  · exact (tri_lt x y _).symm

theorem succ_le_castSucc {m : ℕ} {i j : Fin (m + 1)} (h : i < j) : i.succ ≤ j.castSucc := by
  rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
  exact h

def idx (m : ℕ) : Tgt m → FinalTheorems m
  | Sum.inl _ => Sum.inr ⟨(0, Fin.last (m + 1)), Fin.last_pos⟩
  | Sum.inr (Sum.inl k) => Sum.inr ⟨(0, k.succ.castSucc), by
      rw [Fin.lt_def]; simp⟩
  | Sum.inr (Sum.inr (Sum.inl q)) => cls q.1.1 q.1.2.castSucc (succ_le_castSucc q.2)
  | Sum.inr (Sum.inr (Sum.inr i)) => cls i (Fin.last (m + 1)) (Fin.le_last _)

theorem idx_surjective (m : ℕ) : Function.Surjective (idx m) := by
  rintro (i | ⟨⟨a, b⟩, hab⟩)
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
    · refine ⟨Sum.inr (Sum.inr (Sum.inl ⟨(k.castSucc, k.succ), Fin.castSucc_lt_succ⟩)), ?_⟩
      show cls k.castSucc k.succ.castSucc (succ_le_castSucc Fin.castSucc_lt_succ) = Sum.inl k.castSucc
      unfold cls
      exact dif_pos rfl
    · exact ⟨Sum.inr (Sum.inr (Sum.inr (Fin.last m))), by simp [idx, cls]⟩
  · rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨i, rfl⟩
    · rcases Fin.eq_castSucc_or_eq_last b with ⟨c, rfl⟩ | rfl
      · rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨k, rfl⟩
        · simp at hab
        · exact ⟨Sum.inr (Sum.inl k), rfl⟩
      · exact ⟨Sum.inl (), rfl⟩
    · rcases Fin.eq_castSucc_or_eq_last b with ⟨c, rfl⟩ | rfl
      · have hic : i < c := by
          rw [Fin.lt_def] at hab ⊢
          simp only [Fin.val_succ, Fin.val_castSucc] at hab
          omega
        exact ⟨Sum.inr (Sum.inr (Sum.inl ⟨(i, c), hic⟩)), by simp [idx, cls, ne_of_lt hab]⟩
      · exact ⟨Sum.inr (Sum.inr (Sum.inr i)), by simp [idx, cls, ne_of_lt hab]⟩

theorem card_eq (m : ℕ) : Fintype.card (Tgt m) = Fintype.card (FinalTheorems m) := by
  simp only [Tgt, FinalTheorems, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin,
    Formalism.FourierDecayAlt.P.G5.card_UT, Finset.sum_range_succ]
  ring

theorem idx_bijective (m : ℕ) : Function.Bijective (idx m) :=
  (Fintype.bijective_iff_surjective_and_card _).mpr ⟨idx_surjective m, card_eq m⟩

noncomputable def idxE (m : ℕ) : Tgt m ≃ FinalTheorems m := Equiv.ofBijective (idx m) (idx_bijective m)

def split (m : ℕ) (v : Tgt m → ℂ) : RedCoord m :=
  (v (Sum.inl ()), fun k => v (Sum.inr (Sum.inl k)), fun q => v (Sum.inr (Sum.inr (Sum.inl q))),
    fun i => v (Sum.inr (Sum.inr (Sum.inr i))))

theorem redOf_eq (m : ℕ) (p : XY m) : redOf m p = split m (Sum.elim p.1 p.2 ∘ idx m) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact tri_lt p.1 p.2 Fin.last_pos
  · funext k
    exact tri_lt p.1 p.2 _
  · funext q
    exact (elim_cls p.1 p.2 _ _ (succ_le_castSucc q.2)).symm
  · funext i
    exact (elim_cls p.1 p.2 _ _ (Fin.le_last _)).symm

theorem split_bijective (m : ℕ) : Function.Bijective (split m) := by
  refine ⟨fun v w h => ?_, fun q => ⟨Sum.elim (fun _ => q.1) (Sum.elim q.2.1 (Sum.elim q.2.2.1 q.2.2.2)), rfl⟩⟩
  simp only [split, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  funext s
  rcases s with ⟨⟩ | k | q | i
  · exact h1
  · exact congrFun h2 k
  · exact congrFun h3 q
  · exact congrFun h4 i

theorem elim_bijective (m : ℕ) :
    Function.Bijective (fun p : XY m => (Sum.elim p.1 p.2 : FinalTheorems m → ℂ)) :=
  (Equiv.sumArrowEquivProdArrow _ _ ℂ).symm.bijective

theorem comp_bijective (m : ℕ) : Function.Bijective (fun v : FinalTheorems m → ℂ => v ∘ idx m) := by
  refine ⟨fun v w h => funext fun s => ?_, fun u => ⟨u ∘ (idxE m).symm, funext fun t => ?_⟩⟩
  · obtain ⟨t, rfl⟩ := idx_surjective m s
    exact congrFun h t
  · simp only [Function.comp_apply]
    congr 1
    exact (idxE m).symm_apply_apply t

theorem redOf_bijective (m : ℕ) : Function.Bijective (redOf m) := by
  have h : redOf m = split m ∘ (fun v : FinalTheorems m → ℂ => v ∘ idx m) ∘
      (fun p : XY m => (Sum.elim p.1 p.2 : FinalTheorems m → ℂ)) := funext (redOf_eq m)
  rw [h]
  exact (split_bijective m).comp ((comp_bijective m).comp (elim_bijective m))

theorem mp_elim (β : ℂ) (m : ℕ) :
    MeasurePreserving (fun p : XY m => (Sum.elim p.1 p.2 : FinalTheorems m → ℂ)) (muXY β m) (muPi β (FinalTheorems m)) := by
  have := Formalism.FourierDecayAlt.P.G5.sigmaFinite_mu β
  have h := measurePreserving_sumPiEquivProdPi_symm (X := fun _ : FinalTheorems m => ℂ) (fun _ => mu β)
  have e : (fun p : XY m => (Sum.elim p.1 p.2 : FinalTheorems m → ℂ)) =
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : FinalTheorems m => ℂ)).symm := by
    funext p i
    cases i <;> rfl
  rw [e]
  exact h

theorem mp_split (β : ℂ) (m : ℕ) : MeasurePreserving (split m) (muPi β (Tgt m)) (muRed β m) := by
  have := Formalism.FourierDecayAlt.P.G5.sigmaFinite_mu β
  have h3 := measurePreserving_sumPiEquivProdPi (X := fun _ : UT (m + 1) ⊕ Fin (m + 1) => ℂ)
    (fun _ => mu β)
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin m ⊕ (UT (m + 1) ⊕ Fin (m + 1)) => ℂ)
    (fun _ => mu β)
  have h1 := measurePreserving_sumPiEquivProdPi (X := fun _ : Tgt m => ℂ) (fun _ => mu β)
  have hu := measurePreserving_funUnique (mu β) Unit
  have key := (hu.prod ((MeasurePreserving.id _).prod h3 |>.comp h2)).comp h1
  convert key using 1 <;> rfl

theorem rhs_zero {m : ℕ} (t ρ₁ : ℂ) (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) {j : Fin (m + 2)} (h : 0 < j) :
    (t • subShift (m + 2) + Matrix.diagonal (Fin.cons ρ₁ x : Fin (m + 2) → ℂ) + strictUpper y) 0 j =
      triXY x y 0 j := by
  simp [triXY, subShift, Matrix.diagonal_apply_ne _ h.ne]

theorem rhs_succ {m : ℕ} (t ρ₁ : ℂ) (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) (i : Fin (m + 1))
    (j : Fin (m + 2)) :
    (t • subShift (m + 2) + Matrix.diagonal (Fin.cons ρ₁ x : Fin (m + 2) → ℂ) + strictUpper y) i.succ j =
      (if (j : ℕ) = i then t else 0) + triXY x y i.succ j := by
  simp only [triXY, subShift, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
    Matrix.diagonal_apply, Fin.val_succ, smul_eq_mul, Fin.cons_succ]
  have hiff : ((j : ℕ) + 1 = (i : ℕ) + 1) ↔ ((j : ℕ) = i) := by omega
  by_cases hj : (j : ℕ) = i
  · rw [if_pos (hiff.mpr hj), if_pos hj]
    ring
  · rw [if_neg (fun h => hj (hiff.mp h)), if_neg hj]
    ring

theorem wMat_mulVec_apply {n : ℕ} (B : Fin n → ℂ) (i : Fin n) : (wMat n *ᵥ B) i = B i.rev := by
  simp [wMat, Matrix.mulVec, dotProduct]

theorem xOf_redOf (m : ℕ) (p : XY m) (k : Fin (m + 1)) :
    xOf (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2 k = p.1 k := by
  induction k using Fin.lastCases with
  | last =>
    simp only [xOf, Fin.succ_last, blk_cl]
    exact tri_diag p.1 p.2 (Fin.last m)
  | cast c =>
    simp only [xOf, Fin.succ_castSucc, blk_cc, strictUpper, Matrix.of_apply,
      dif_pos (Fin.castSucc_lt_succ (i := c))]
    exact tri_diag p.1 p.2 c.castSucc

theorem matrix_redOf (m : ℕ) (t ρ₁ : ℂ) (p : XY m) :
    wMat (m + 2) * Mcoord t (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2
        (Fin.cons ρ₁ (redOf m p).2.1) (redOf m p).1 =
      t • subShift (m + 2) + Matrix.diagonal (Fin.cons ρ₁ p.1 : Fin (m + 2) → ℂ) + strictUpper p.2 := by
  ext i j
  rw [wMat_mul_apply]
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨r, rfl⟩
  ·
    rw [Fin.rev_zero]
    rcases Fin.eq_castSucc_or_eq_last j with ⟨c, rfl⟩ | rfl
    · rw [Mcoord, blk_lc]
      rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨k, rfl⟩
      · simp [subShift, strictUpper]
      · rw [Fin.cons_succ, rhs_zero _ _ _ _ (by simp [Fin.lt_def])]
        rfl
    · rw [Mcoord, blk_ll, rhs_zero _ _ _ _ Fin.last_pos]
      rfl
  ·
    rw [Fin.rev_succ, rhs_succ]
    rcases Fin.eq_castSucc_or_eq_last j with ⟨c, rfl⟩ | rfl
    · rw [Mcoord, blk_cc, wMat_mul_apply, Fin.rev_rev]
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, strictUpper,
        Matrix.of_apply, Fin.val_castSucc, smul_eq_mul]
      by_cases hrc : r < c
      · have h1 : r ≠ c := ne_of_lt hrc
        have h2 : (c : ℕ) ≠ r := fun h => h1 (Fin.ext h.symm)
        rw [dif_pos hrc, if_neg h1, if_neg h2]
        simp only [mul_zero, zero_add]
        rfl
      · have hcr : c.castSucc < r.succ := by
          rw [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
          rw [not_lt, Fin.le_iff_val_le_val] at hrc
          omega
        rw [dif_neg hrc, tri_gt _ _ hcr]
        by_cases hrc' : r = c
        · subst hrc'
          simp
        · have h2 : (c : ℕ) ≠ r := fun h => hrc' (Fin.ext h.symm)
          simp [hrc', h2]
    · rw [Mcoord, blk_cl, wMat_mulVec_apply, Fin.rev_rev]
      have hne : ((Fin.last (m + 1) : Fin (m + 2)) : ℕ) ≠ r := by
        simp only [Fin.val_last]
        have := r.isLt
        omega
      rw [if_neg hne, zero_add]
      rfl

theorem strictUpper_injective {d : ℕ} {y y' : UT d → ℂ} {a b : Fin d → ℂ}
    (h : Matrix.diagonal a + strictUpper y = Matrix.diagonal b + strictUpper y') : y = y' := by
  funext q
  obtain ⟨⟨i, j⟩, hij⟩ := q
  have h' := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j) h
  simpa [strictUpper, hij, Matrix.diagonal_apply_ne _ hij.ne] using h'

theorem diag_const (m : ℕ) (z : ℂ) :
    Matrix.diagonal (Fin.cons z (fun _ : Fin (m + 1) => z) : Fin (m + 2) → ℂ) =
      z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) := by
  have hc : (Fin.cons z (fun _ : Fin (m + 1) => z) : Fin (m + 2) → ℂ) = fun _ => z := by
    funext i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩ <;> simp
  rw [hc, Matrix.smul_one_eq_diagonal]

end Formalism.FourierDecayAlt.P.WeakApproximationGL

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.WeakApproximationGL

theorem split_xy_coordinates : Formalism.FourierDecayAlt.G.SplitXY := by
  intro m β
  refine ⟨redOf_bijective m, ?_⟩
  have h : redOf m = split m ∘ (fun v : FinalTheorems m → ℂ => v ∘ idx m) ∘
      (fun p : XY m => (Sum.elim p.1 p.2 : FinalTheorems m → ℂ)) := funext (redOf_eq m)
  rw [h]
  exact (mp_split β m).comp ((Formalism.FourierDecayAlt.P.G5.mp_comp_equiv β (idxE m)).comp (mp_elim β m))

theorem split_xy_matrix : Formalism.FourierDecayAlt.G.SplitXYMatrix :=
  fun m t ρ₁ p => ⟨xOf_redOf m p, matrix_redOf m t ρ₁ p⟩

theorem limit_coordinates : Formalism.FourierDecayAlt.G.LimitCoords := by
  intro m z y
  refine ⟨redOf m (fun _ => z, y), ⟨fun k => xOf_redOf m _ k, ?_⟩, ?_⟩
  · rw [matrix_redOf, zero_smul, zero_add]
    dsimp only
    rw [diag_const]
  · rintro q ⟨hx, hM⟩
    obtain ⟨p', rfl⟩ := (redOf_bijective m).2 q
    have h1 : p'.1 = fun _ => z := funext fun k => (xOf_redOf m p' k).symm.trans (hx k)
    rw [matrix_redOf, zero_smul, zero_add, ← diag_const] at hM
    have h2 : p'.2 = y := strictUpper_injective hM
    rw [show p' = (fun _ => z, y) from Prod.ext h1 h2]

end Formalism.FourierDecayAlt.P
