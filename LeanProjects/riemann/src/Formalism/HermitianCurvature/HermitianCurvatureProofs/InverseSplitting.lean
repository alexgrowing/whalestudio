import Formalism.HermitianCurvature.HermitianCurvatureProofs.RelevantMonotoneOfParts

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

namespace InverseSplitting

open C2x2

variable {m : ℕ}

noncomputable def lsStep (w : Equiv.Perm (Fin m)) (l : Matrix (Fin m) (Fin m) ℂ) :
    ℕ → Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ
  | 0 => (1, 1)
  | n + 1 =>
    (Matrix.of fun i j => if i.val = j.val + n + 1 then
        (if w.symm j < w.symm i then l i j - ((lsStep w l n).1 * (lsStep w l n).2) i j else 0)
        else (lsStep w l n).1 i j,
     Matrix.of fun i j => if i.val = j.val + n + 1 then
        (if w.symm j < w.symm i then 0 else l i j - ((lsStep w l n).1 * (lsStep w l n).2) i j)
        else (lsStep w l n).2 i j)

structure Inv (w : Equiv.Perm (Fin m)) (l : Matrix (Fin m) (Fin m) ℂ) (n : ℕ)
    (A B : Matrix (Fin m) (Fin m) ℂ) : Prop where
  up : ∀ i j : Fin m, i < j → A i j = 0 ∧ B i j = 0
  diag : ∀ i, A i i = 1 ∧ B i i = 1
  far : ∀ i j : Fin m, j.val + n < i.val → A i j = 0 ∧ B i j = 0
  supA : ∀ i j : Fin m, j < i → ¬ (w.symm j < w.symm i) → A i j = 0
  supB : ∀ i j : Fin m, j < i → w.symm j < w.symm i → B i j = 0
  prod : ∀ i j : Fin m, i.val ≤ j.val + n → (A * B) i j = l i j

lemma inv_step (w : Equiv.Perm (Fin m)) (l : Matrix (Fin m) (Fin m) ℂ) (hl : l ∈ C2.LTset m) :
    ∀ n, Inv w l n (lsStep w l n).1 (lsStep w l n).2 := by
  intro n
  induction n with
  | zero =>
    show Inv w l 0 1 1
    refine ⟨fun i j h => ?_, fun i => by simp, fun i j h => ?_, fun i j h _ => ?_,
      fun i j h _ => ?_, fun i j h => ?_⟩
    · have hne : i ≠ j := ne_of_lt h
      simp [Matrix.one_apply_ne hne]
    · have hne : i ≠ j := fun e => by subst e; omega
      simp [Matrix.one_apply_ne hne]
    · simp [Matrix.one_apply_ne (ne_of_lt h).symm]
    · simp [Matrix.one_apply_ne (ne_of_lt h).symm]
    · rw [Matrix.one_mul]
      by_cases hij : i = j
      · subst hij
        simp [hl.2 i]
      · have hlt : i < j := by
          have hv : i.val ≠ j.val := fun e => hij (Fin.ext e)
          rw [Fin.lt_iff_val_lt_val]
          omega
        rw [Matrix.one_apply_ne hij, hl.1 i j hlt]
  | succ n ih =>
    obtain ⟨hup, hdiag, hfar, hsupA, hsupB, hprod⟩ := ih
    set A := (lsStep w l n).1 with hAdef
    set B := (lsStep w l n).2 with hBdef
    have hA' : ∀ i j, (lsStep w l (n + 1)).1 i j = if i.val = j.val + n + 1 then
        (if w.symm j < w.symm i then l i j - (A * B) i j else 0) else A i j := fun i j => rfl
    have hB' : ∀ i j, (lsStep w l (n + 1)).2 i j = if i.val = j.val + n + 1 then
        (if w.symm j < w.symm i then 0 else l i j - (A * B) i j) else B i j := fun i j => rfl
    refine ⟨fun i j h => ?_, fun i => ?_, fun i j h => ?_, fun i j h hw => ?_,
      fun i j h hw => ?_, fun i j h => ?_⟩
    · have hv : ¬ i.val = j.val + n + 1 := by
        rw [Fin.lt_iff_val_lt_val] at h
        omega
      rw [hA', hB', if_neg hv, if_neg hv]
      exact hup i j h
    · have hv : ¬ i.val = i.val + n + 1 := by omega
      rw [hA', hB', if_neg hv, if_neg hv]
      exact hdiag i
    · have hv : ¬ i.val = j.val + n + 1 := by omega
      rw [hA', hB', if_neg hv, if_neg hv]
      exact hfar i j (by omega)
    · rw [hA']
      split_ifs with hv
      · rfl
      · exact hsupA i j h hw
    · rw [hB']
      split_ifs with hv
      · rfl
      · exact hsupB i j h hw
    · rw [Matrix.mul_apply]
      by_cases hgap : i.val = j.val + n + 1
      ·
        have hji : j ≠ i := fun e => by subst e; omega
        have hAij : A i j = 0 := (hfar i j (by omega)).1
        have hBij : B i j = 0 := (hfar i j (by omega)).2
        have hterm : ∀ k, (lsStep w l (n + 1)).1 i k * (lsStep w l (n + 1)).2 k j =
            A i k * B k j + (if k = j then (lsStep w l (n + 1)).1 i j else 0) +
              (if k = i then (lsStep w l (n + 1)).2 i j else 0) := by
          intro k
          by_cases hkj : k = j
          · subst hkj
            have hv : ¬ k.val = k.val + n + 1 := by omega
            rw [hB' k k, if_neg hv, (hdiag k).2, hAij, if_pos rfl, if_neg hji]
            simp
          by_cases hki : k = i
          · subst hki
            have hv : ¬ k.val = k.val + n + 1 := by omega
            rw [hA' k k, if_neg hv, (hdiag k).1, hBij, if_neg hkj, if_pos rfl]
            simp
          have hv1 : ¬ i.val = k.val + n + 1 := fun e => hkj (Fin.ext (by omega))
          have hv2 : ¬ k.val = j.val + n + 1 := fun e => hki (Fin.ext (by omega))
          rw [hA' i k, hB' k j, if_neg hv1, if_neg hv2, if_neg hkj, if_neg hki]
          simp
        rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_ite_eq' Finset.univ j, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _),
          if_pos (Finset.mem_univ _), ← Matrix.mul_apply, hA', hB', if_pos hgap, if_pos hgap]
        split_ifs <;> ring
      ·
        have hle : i.val ≤ j.val + n := by omega
        rw [← hprod i j hle, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk1 : i.val = k.val + n + 1
        · have hkj : k < j := by
            rw [Fin.lt_iff_val_lt_val]
            omega
          have hv2 : ¬ k.val = j.val + n + 1 := by omega
          rw [hB' k j, if_neg hv2, (hup k j hkj).2]
          simp
        · rw [hA' i k, if_neg hk1]
          by_cases hk2 : k.val = j.val + n + 1
          · have hik : i < k := by
              rw [Fin.lt_iff_val_lt_val]
              omega
            rw [(hup i k hik).1]
            simp
          · rw [hB' k j, if_neg hk2]

end InverseSplitting

open C2x2 InverseSplitting

lemma conj_mul_eq_mul_conj {m : ℕ} (P X Y : Matrix (Fin m) (Fin m) ℂ) (hP : IsUnit P.det) :
    P⁻¹ * (X * Y) * P = (P⁻¹ * X * P) * (P⁻¹ * Y * P) := by
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hP]

lemma conj_inv_eq_inv_conj {m : ℕ} (P X : Matrix (Fin m) (Fin m) ℂ) (hP : IsUnit P.det) :
    (P⁻¹ * X * P)⁻¹ = P⁻¹ * X⁻¹ * P := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv P hP, Matrix.mul_assoc]

private lemma mul_mem_ltset {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.LTset m)
    (hB : B ∈ C2.LTset m) : A * B ∈ C2.LTset m := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : i < k
    · rw [hA.1 i k hik, zero_mul]
    · rw [hB.1 k j (lt_of_le_of_lt (not_lt.1 hik) h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.2 i, hB.2 i, one_mul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [hB.1 k i h, mul_zero]
      · rw [hA.1 i k h, zero_mul]
    · simp

private lemma mul_mem_utset {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.UTset m)
    (hB : B ∈ C2.UTset m) : A * B ∈ C2.UTset m := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hki : k < i
    · rw [hA.1 i k hki, zero_mul]
    · rw [hB.1 k j (lt_of_lt_of_le h (not_lt.1 hki)), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.2 i, hB.2 i, one_mul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [hA.1 i k h, zero_mul]
      · rw [hB.1 k i h, mul_zero]
    · simp

private lemma det_eq_one_of_mem_ltset {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.LTset m) :
    A.det = 1 := by
  rw [Matrix.det_of_lowerTriangular A (fun i j h => hA.1 i j h)]
  simp [hA.2]

private lemma det_eq_one_of_mem_utset {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.UTset m) :
    A.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j h => hA.1 i j h)]
  simp [hA.2]

private lemma inv_mem_ltset {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.LTset m) :
    A⁻¹ ∈ C2.LTset m := by
  have hbt : A.BlockTriangular OrderDual.toDual := fun i j h => hA.1 i j h
  have hdet : IsUnit A.det := by rw [det_eq_one_of_mem_ltset hA]; exact isUnit_one
  haveI := A.invertibleOfIsUnitDet hdet
  have hbi := Matrix.blockTriangular_inv_of_blockTriangular hbt
  refine ⟨fun i j h => hbi h, fun i => ?_⟩
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv A hdet) i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, hA.2 i, one_mul] at h1
  · simpa using h1
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hbi h, mul_zero]
    · rw [hA.1 i k h, zero_mul]
  · simp

private lemma inv_mem_utset {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.UTset m) :
    A⁻¹ ∈ C2.UTset m := by
  have hbt : A.BlockTriangular id := fun i j h => hA.1 i j h
  have hdet : IsUnit A.det := by rw [det_eq_one_of_mem_utset hA]; exact isUnit_one
  haveI := A.invertibleOfIsUnitDet hdet
  have hbi := Matrix.blockTriangular_inv_of_blockTriangular hbt
  refine ⟨fun i j h => hbi h, fun i => ?_⟩
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv A hdet) i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, hA.2 i, one_mul] at h1
  · simpa using h1
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hA.1 i k h, zero_mul]
    · rw [hbi h, mul_zero]
  · simp

theorem lower_triangular_splitting : C2.LowSplit := by
  intro m P hP l hl
  obtain ⟨w, d, hd, rfl⟩ := hP
  set Q : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun a i => if i = w a then (d a)⁻¹ else 0 with hQ
  have hQP : Q * C2.monoP w d = 1 := by
    ext a b
    rw [Matrix.mul_apply]
    simp only [hQ, C2.monoP, Matrix.of_apply, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hab : a = b
    · subst hab
      simp [hd a]
    · simp [Matrix.one_apply_ne hab, w.injective.ne hab, Ne.symm hab]
  have hPinv : (C2.monoP w d)⁻¹ = Q := Matrix.inv_eq_left_inv hQP
  have hPdet : IsUnit (C2.monoP w d).det := Matrix.isUnit_det_of_left_inverse hQP
  have hconj : ∀ (X : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m),
      ((C2.monoP w d)⁻¹ * X * C2.monoP w d) a b = (d a)⁻¹ * X (w a) (w b) * d b := by
    intro X a b
    rw [hPinv, Matrix.mul_apply]
    simp only [Matrix.mul_apply, hQ, C2.monoP, Matrix.of_apply, ite_mul, zero_mul, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have I := inv_step w l hl m
  set A := (lsStep w l m).1 with hAdef
  set B := (lsStep w l m).2 with hBdef
  have hAB : l = A * B := by
    ext i j
    exact (I.prod i j (by omega)).symm
  have hAL : A ∈ C2.LTset m := ⟨fun i j h => (I.up i j h).1, fun i => (I.diag i).1⟩
  have hBL : B ∈ C2.LTset m := ⟨fun i j h => (I.up i j h).2, fun i => (I.diag i).2⟩
  have hAc : (C2.monoP w d)⁻¹ * A * C2.monoP w d ∈ C2.LTset m := by
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · rw [hconj]
      rcases lt_trichotomy (w a) (w b) with h | h | h
      · rw [(I.up _ _ h).1]
        simp
      · exact absurd (w.injective h) (ne_of_lt hab)
      · rw [I.supA _ _ h (by simpa using (not_lt.2 hab.le))]
        simp
    · rw [hconj, (I.diag (w a)).1]
      field_simp [hd a]
  have hBc : (C2.monoP w d)⁻¹ * B * C2.monoP w d ∈ C2.UTset m := by
    refine ⟨fun a b hba => ?_, fun a => ?_⟩
    · rw [hconj]
      rcases lt_trichotomy (w a) (w b) with h | h | h
      · rw [(I.up _ _ h).2]
        simp
      · exact absurd (w.injective h) (ne_of_lt hba).symm
      · rw [I.supB _ _ h (by simpa using hba)]
        simp
    · rw [hconj, (I.diag (w a)).2]
      field_simp [hd a]
  refine ⟨(A, B), ⟨⟨hAL, hAc⟩, ⟨hBL, hBc⟩, hAB⟩, ?_⟩
  rintro ⟨A2, B2⟩ ⟨hA2, hB2, hl2⟩
  have hl2' : l = A2 * B2 := hl2
  have hAdet : IsUnit A.det := by rw [det_eq_one_of_mem_ltset hAL]; exact isUnit_one
  have hB2det : IsUnit B2.det := by rw [det_eq_one_of_mem_ltset hB2.1]; exact isUnit_one
  have hkey : A⁻¹ * A2 = B * B2⁻¹ := by
    calc A⁻¹ * A2 = A⁻¹ * A2 * (B2 * B2⁻¹) := by
          rw [Matrix.mul_nonsing_inv B2 hB2det, Matrix.mul_one]
      _ = A⁻¹ * (A2 * B2) * B2⁻¹ := by simp only [Matrix.mul_assoc]
      _ = A⁻¹ * (A * B) * B2⁻¹ := by rw [← hl2', ← hAB]
      _ = B * B2⁻¹ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hAdet, Matrix.one_mul]
  have hYL : (C2.monoP w d)⁻¹ * (A⁻¹ * A2) * C2.monoP w d ∈ C2.LTset m := by
    rw [conj_mul_eq_mul_conj _ _ _ hPdet, ← conj_inv_eq_inv_conj _ _ hPdet]
    exact mul_mem_ltset (inv_mem_ltset hAc) hA2.2
  have hYU : (C2.monoP w d)⁻¹ * (A⁻¹ * A2) * C2.monoP w d ∈ C2.UTset m := by
    rw [hkey, conj_mul_eq_mul_conj _ _ _ hPdet, ← conj_inv_eq_inv_conj _ _ hPdet]
    exact mul_mem_utset hBc (inv_mem_utset hB2.2)
  have hY : (C2.monoP w d)⁻¹ * (A⁻¹ * A2) * C2.monoP w d = 1 := by
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · rw [hYL.1 i j h, Matrix.one_apply_ne (ne_of_lt h)]
    · subst h
      rw [hYL.2 i, Matrix.one_apply_eq]
    · rw [hYU.1 i j h, Matrix.one_apply_ne (ne_of_lt h).symm]
  have hZ : A⁻¹ * A2 = 1 := by
    calc A⁻¹ * A2 = C2.monoP w d * ((C2.monoP w d)⁻¹ * (A⁻¹ * A2) * C2.monoP w d) *
          (C2.monoP w d)⁻¹ := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPdet, Matrix.mul_one,
            Matrix.mul_nonsing_inv_cancel_left _ _ hPdet]
      _ = 1 := by rw [hY, Matrix.mul_one, Matrix.mul_nonsing_inv _ hPdet]
  have hA2A : A2 = A := by
    calc A2 = A * (A⁻¹ * A2) := (Matrix.mul_nonsing_inv_cancel_left A A2 hAdet).symm
      _ = A := by rw [hZ, Matrix.mul_one]
  have hB2B : B2 = B := by
    calc B2 = A⁻¹ * (A * B2) := (Matrix.nonsing_inv_mul_cancel_left A B2 hAdet).symm
      _ = A⁻¹ * (A * B) := by rw [← hA2A, ← hl2', hAB, hA2A]
      _ = B := Matrix.nonsing_inv_mul_cancel_left A B hAdet
  rw [hA2A, hB2B]

private lemma conjTranspose_mem_ltset_of_mem_utset {m : ℕ} {v : Matrix (Fin m) (Fin m) ℂ} (hv : v ∈ C2.UTset m) :
    vᴴ ∈ C2.LTset m :=
  ⟨fun i j h => by simp [Matrix.conjTranspose_apply, hv.1 j i h],
    fun i => by simp [Matrix.conjTranspose_apply, hv.2 i]⟩

private lemma conjTranspose_mem_utset_of_mem_ltset {m : ℕ} {v : Matrix (Fin m) (Fin m) ℂ} (hv : v ∈ C2.LTset m) :
    vᴴ ∈ C2.UTset m :=
  ⟨fun i j h => by simp [Matrix.conjTranspose_apply, hv.1 j i h],
    fun i => by simp [Matrix.conjTranspose_apply, hv.2 i]⟩

theorem upper_splitting : C2.UpSplit := by
  intro m P hP u hu
  obtain ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, huniq⟩ := lower_triangular_splitting m P hP uᴴ (conjTranspose_mem_ltset_of_mem_utset hu)
  refine ⟨(bᴴ, aᴴ), ⟨conjTranspose_mem_utset_of_mem_ltset hb.1, conjTranspose_mem_utset_of_mem_ltset ha.1,
    by simpa only [Matrix.conjTranspose_conjTranspose] using hb,
    by simpa only [Matrix.conjTranspose_conjTranspose] using ha, ?_⟩, ?_⟩
  · have hab' : uᴴ = a * b := hab
    show u = bᴴ * aᴴ
    rw [← Matrix.conjTranspose_mul, ← hab', Matrix.conjTranspose_conjTranspose]
  · rintro ⟨q1, q2⟩ ⟨_, _, hq1c, hq2c, hq⟩
    have hq' : u = q1 * q2 := hq
    have h := huniq (q2ᴴ, q1ᴴ) ⟨hq2c, hq1c, by
      show uᴴ = q2ᴴ * q1ᴴ
      rw [← Matrix.conjTranspose_mul, ← hq']⟩
    simp only [Prod.mk.injEq] at h
    rw [← h.1, ← h.2, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose]

end Formalism.FourierDecayAlt.P
