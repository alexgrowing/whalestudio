import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens

noncomputable section

open Finset Matrix MeasureTheory InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

lemma qrA_Jm_one : Jm (fun _ : Fin N => true) = 1 := by
  unfold Jm
  simp

lemma qrA_unitary (k : UNgrp N) : (toM k)ᴴ * toM k = 1 := by
  have h : (toM k)ᴴ * Jm (fun _ : Fin N => true) * toM k = Jm (fun _ : Fin N => true) := k.2
  rwa [qrA_Jm_one, Matrix.mul_one] at h

lemma qrA_upMat_continuous : Continuous (upMat (N := N)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  by_cases hab : a = b
  · simp only [upMat, if_pos hab]
    exact Complex.continuous_ofReal.comp ((continuous_apply a).comp continuous_fst)
  · by_cases h : a < b
    · simp only [upMat, if_neg hab, dif_pos h]
      exact (continuous_apply _).comp continuous_snd
    · simp only [upMat, if_neg hab, dif_neg h]
      exact continuous_const

theorem qrMap_continuous : Continuous (qrMap (N := N)) := by
  show Continuous fun kt : UNgrp N × TriCo N => toM kt.1 * upMat kt.2
  exact ((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst).matrix_mul
    (qrA_upMat_continuous.comp continuous_snd)

lemma qrA_upMat_tri (t : TriCo N) : (upMat t).IsUpperTriangular := by
  intro i j hij
  have h1 : i ≠ j := ne_of_gt hij
  have h2 : ¬ i < j := not_lt.2 (le_of_lt hij)
  simp only [upMat, if_neg h1, dif_neg h2]

lemma qrA_upMat_diag (t : TriCo N) (i : Fin N) : upMat t i i = ((t.1 i : ℝ) : ℂ) := by
  simp [upMat]

lemma qrA_upMat_det (t : TriCo N) : (upMat t).det = ∏ j, ((t.1 j : ℝ) : ℂ) := by
  rw [Matrix.det_of_upperTriangular (qrA_upMat_tri t)]
  exact Finset.prod_congr rfl fun i _ => qrA_upMat_diag t i

lemma qrA_upMat_det_ne (t : TriCo N) (ht : t ∈ triPos N) : (upMat t).det ≠ 0 := by
  rw [qrA_upMat_det]
  exact Finset.prod_ne_zero_iff.2 fun j _ => Complex.ofReal_ne_zero.2 (ht j).ne'

lemma qrA_triCoOf_upMat (t : TriCo N) : triCoOf (upMat t) = t := by
  refine Prod.ext (funext fun j => ?_) (funext fun ab => ?_)
  · simp [triCoOf, upMat]
  · simp only [triCoOf, upMat, if_neg (ne_of_lt ab.2), dif_pos ab.2]

lemma qrA_mul_diag {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsUpperTriangular)
    (hB : B.IsUpperTriangular) (i : Fin N) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

lemma qrA_inv_tri {R : Matrix (Fin N) (Fin N) ℂ} (hR : R.IsUpperTriangular) (hd : R.det ≠ 0) :
    (R⁻¹).IsUpperTriangular := by
  haveI : Invertible R := R.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hd)
  exact Matrix.blockTriangular_inv_of_blockTriangular hR

lemma qrA_upMat_cancel {A B : Matrix (Fin N) (Fin N) ℂ} {R : Matrix (Fin N) (Fin N) ℂ} (hd : R.det ≠ 0)
    (h : A * R = B * R) : A = B := by
  have hu : IsUnit R.det := isUnit_iff_ne_zero.2 hd
  calc A = A * R * R⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = B * R * R⁻¹ := by rw [h]
    _ = B := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

lemma qrA_tri_unique {U R R' : Matrix (Fin N) (Fin N) ℂ} {t t' : TriCo N} (ht : t ∈ triPos N)
    (ht' : t' ∈ triPos N) (hR : R = upMat t) (hR' : R' = upMat t')
    (h1 : U * R = R') (h2 : Uᴴ * R' = R) : t = t' := by
  subst hR
  subst hR'
  have hd := qrA_upMat_det_ne t ht
  have hd' := qrA_upMat_det_ne t' ht'
  have hRt := qrA_upMat_tri t
  have hRt' := qrA_upMat_tri t'
  have hu : IsUnit (upMat t).det := isUnit_iff_ne_zero.2 hd
  have hu' : IsUnit (upMat t').det := isUnit_iff_ne_zero.2 hd'
  have hU : U = upMat t' * (upMat t)⁻¹ := by
    rw [← h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have hUh : Uᴴ = upMat t * (upMat t')⁻¹ := by
    rw [← h2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu', Matrix.mul_one]
  have hUt : U.IsUpperTriangular := hU ▸ hRt'.mul (qrA_inv_tri hRt hd)
  have hUht : Uᴴ.IsUpperTriangular := hUh ▸ hRt.mul (qrA_inv_tri hRt' hd')
  have hinvd : ∀ M : Matrix (Fin N) (Fin N) ℂ, M.IsUpperTriangular → M.det ≠ 0 →
      ∀ i, M⁻¹ i i = (M i i)⁻¹ := by
    intro M hM hMd i
    have h := congrFun (congrFun (Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.2 hMd)) i) i
    rw [qrA_mul_diag hM (qrA_inv_tri hM hMd), Matrix.one_apply_eq] at h
    exact eq_inv_of_mul_eq_one_right h
  have hdiag : ∀ i, U i i = ((t'.1 i : ℝ) : ℂ) * (((t.1 i : ℝ) : ℂ))⁻¹ := by
    intro i
    rw [hU, qrA_mul_diag hRt' (qrA_inv_tri hRt hd), hinvd _ hRt hd, qrA_upMat_diag, qrA_upMat_diag]
  have hdiag' : ∀ i, Uᴴ i i = ((t.1 i : ℝ) : ℂ) * (((t'.1 i : ℝ) : ℂ))⁻¹ := by
    intro i
    rw [hUh, qrA_mul_diag hRt (qrA_inv_tri hRt' hd'), hinvd _ hRt' hd', qrA_upMat_diag, qrA_upMat_diag]
  have heq : ∀ i, t.1 i = t'.1 i := by
    intro i
    have e1 := hdiag' i
    rw [Matrix.conjTranspose_apply, hdiag i] at e1
    have ha := ht i
    have hb := ht' i
    have e2 : t'.1 i * (t.1 i)⁻¹ = t.1 i * (t'.1 i)⁻¹ := by
      have e3 : ((t'.1 i * (t.1 i)⁻¹ : ℝ) : ℂ) = ((t.1 i * (t'.1 i)⁻¹ : ℝ) : ℂ) := by
        push_cast
        rw [← e1]
        simp [Complex.conj_ofReal]
      exact_mod_cast e3
    field_simp at e2
    nlinarith
  have hU1 : U = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [hdiag i, heq i, Matrix.one_apply_eq]
      exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 (ht' i).ne')
    · rw [Matrix.one_apply_ne hij]
      rcases lt_or_gt_of_ne hij with h | h
      · have e := hUht h
        rw [Matrix.conjTranspose_apply] at e
        simpa using e
      · exact hUt h
  rw [hU1, Matrix.one_mul] at h1
  rw [← qrA_triCoOf_upMat t, h1, qrA_triCoOf_upMat]

theorem qrMap_injOn : Set.InjOn (qrMap (N := N)) (Set.univ ×ˢ triPos N) := by
  rintro ⟨k, t⟩ ⟨-, ht⟩ ⟨k', t'⟩ ⟨-, ht'⟩ h
  have h' : toM k * upMat t = toM k' * upMat t' := h
  have e1 : (toM k')ᴴ * toM k * upMat t = upMat t' := by
    rw [Matrix.mul_assoc, h', ← Matrix.mul_assoc, qrA_unitary, Matrix.one_mul]
  have e2 : ((toM k')ᴴ * toM k)ᴴ * upMat t' = upMat t := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, ← h',
      ← Matrix.mul_assoc, qrA_unitary, Matrix.one_mul]
  have htt : t = t' := qrA_tri_unique ht ht' rfl rfl e1 e2
  subst htt
  have hk : toM k = toM k' := qrA_upMat_cancel (qrA_upMat_det_ne t ht) h'
  have hk' : k = k' := Subtype.ext (Units.ext hk)
  rw [hk']

private theorem qrMap_measurableSet_image_lemma (N : ℕ) : PolishSpace (UNgrp N) := by
  obtain ⟨C, hC, hmem⟩ : ∃ C : Set (Fin N → Fin N → ℂ), IsClosed C ∧
      ∀ Z, Z ∈ C ↔ (Matrix.of Z)ᴴ * Matrix.of Z = 1 :=
    ⟨{Z | (Matrix.of Z)ᴴ * Matrix.of Z = 1},
      isClosed_eq ((continuous_id : Continuous fun Z : Fin N → Fin N → ℂ => Matrix.of Z).matrix_conjTranspose.matrix_mul
        (continuous_id : Continuous fun Z : Fin N → Fin N → ℂ => Matrix.of Z)) continuous_const,
      fun Z => Iff.rfl⟩
  haveI : PolishSpace C := hC.polishSpace
  have hCt : Continuous (fun Z : C => (Z : Fin N → Fin N → ℂ)) := continuous_subtype_val
  let e : UNgrp N ≃ₜ C :=
    { toFun := fun k => ⟨Matrix.of.symm (toM k), (hmem _).2 (qrA_unitary k)⟩
      invFun := fun Z => ⟨⟨Matrix.of Z.1, (Matrix.of Z.1)ᴴ, mul_eq_one_comm.1 ((hmem _).1 Z.2),
          (hmem _).1 Z.2⟩, by
        show (Matrix.of Z.1)ᴴ * Jm (fun _ : Fin N => true) * Matrix.of Z.1 = Jm (fun _ : Fin N => true)
        rw [qrA_Jm_one, Matrix.mul_one]
        exact (hmem _).1 Z.2⟩
      left_inv := fun k => Subtype.ext (Units.ext rfl)
      right_inv := fun Z => rfl
      continuous_toFun := continuous_induced_rng.2
        (Units.continuous_val.comp continuous_subtype_val :
          Continuous fun k : UNgrp N => ((k : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Matrix (Fin N) (Fin N) ℂ))
      continuous_invFun := continuous_induced_rng.2 (Units.continuous_iff.2
        ⟨hCt, hCt.matrix_conjTranspose⟩) }
  exact e.isClosedEmbedding.polishSpace

theorem qrMap_measurableSet_image (S : Set (UNgrp N × TriCo N)) (hS : MeasurableSet S)
    (hS0 : S ⊆ Set.univ ×ˢ triPos N) : MeasurableSet (qrMap '' S) := by
  haveI : PolishSpace (UNgrp N) := qrMap_measurableSet_image_lemma N
  exact hS.image_of_continuousOn_injOn qrMap_continuous.continuousOn (qrMap_injOn.mono hS0)

lemma qrA_exists (Z : Matrix (Fin N) (Fin N) ℂ) (hZ : Z.det ≠ 0) :
    ∃ Q : Matrix (Fin N) (Fin N) ℂ, ∃ t : TriCo N, Qᴴ * Q = 1 ∧ t ∈ triPos N ∧ Q * upMat t = Z := by
  classical
  let f : Fin N → EuclideanSpace ℂ (Fin N) := fun j => WithLp.toLp 2 (Z.col j)
  have hli : LinearIndependent ℂ f := by
    have h0 := Matrix.linearIndependent_cols_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det Z).2 (isUnit_iff_ne_zero.2 hZ))
    exact h0.map' (WithLp.linearEquiv 2 ℂ (Fin N → ℂ)).symm.toLinearMap (LinearEquiv.ker _)
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) = Fintype.card (Fin N) := by simp
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis hdim f
  have hgs : ∀ j, InnerProductSpace.gramSchmidt ℂ f j ≠ 0 := fun j =>
    InnerProductSpace.gramSchmidt_ne_zero j hli
  have hb : ∀ i, b i = InnerProductSpace.gramSchmidtNormed ℂ f i := by
    intro i
    refine InnerProductSpace.gramSchmidtOrthonormalBasis_apply hdim ?_
    intro h
    have := InnerProductSpace.gramSchmidtNormed_unit_length i hli
    rw [h, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin N) (Fin N) ℂ, ∀ a i, Q a i = (b i).ofLp a :=
    ⟨Matrix.of fun a i => (b i).ofLp a, fun _ _ => rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : Matrix (Fin N) (Fin N) ℂ, ∀ i j, R i j = inner ℂ (b i) (f j) :=
    ⟨Matrix.of fun i j => inner ℂ (b i) (f j), fun _ _ => rfl⟩
  have hRup : R.IsUpperTriangular := by
    intro i j hji
    rw [hRdef]
    exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular hdim f hji
  have hself : ∀ j, inner ℂ (InnerProductSpace.gramSchmidt ℂ f j) (f j) =
      (‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℂ) ^ 2 := by
    intro j
    have hf : f j = InnerProductSpace.gramSchmidt ℂ f j +
        ∑ i ∈ Finset.Iio j, (ℂ ∙ InnerProductSpace.gramSchmidt ℂ f i).starProjection (f j) := by
      rw [InnerProductSpace.gramSchmidt_def ℂ f j]
      abel
    rw [hf, inner_add_right, inner_sum, Finset.sum_eq_zero (fun i hi => ?_), add_zero,
      inner_self_eq_norm_sq_to_K]
    · rfl
    · rw [Submodule.starProjection_singleton, inner_smul_right,
        InnerProductSpace.gramSchmidt_orthogonal ℂ f (ne_of_gt (Finset.mem_Iio.1 hi)), mul_zero]
  have hdiag : ∀ j, R j j = ((‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℝ) : ℂ) := by
    intro j
    have ha : ‖InnerProductSpace.gramSchmidt ℂ f j‖ ≠ 0 := norm_ne_zero_iff.2 (hgs j)
    rw [hRdef, hb j, InnerProductSpace.gramSchmidtNormed, inner_smul_left, hself j]
    simp only [map_inv₀, RCLike.conj_ofReal, Complex.conj_ofReal]
    change (((‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℝ) : ℂ))⁻¹ *
        ((‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℝ) : ℂ) ^ 2 = ((‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℝ) : ℂ)
    have hc : ((‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha
    rw [sq, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have ht : triCoOf R ∈ triPos N := by
    intro j
    show 0 < (R j j).re
    rw [hdiag j, Complex.ofReal_re]
    exact norm_pos_iff.2 (hgs j)
  have hupR : upMat (triCoOf R) = R := by
    ext a c
    by_cases hac : a = c
    · subst hac
      simp only [upMat, triCoOf, if_true]
      rw [hdiag a, Complex.ofReal_re]
    · by_cases h : a < c
      · simp only [upMat, triCoOf, if_neg hac, dif_pos h]
      · simp only [upMat, if_neg hac, dif_neg h]
        exact (hRup (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hac))).symm
  have hQ : Qᴴ * Q = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have e := (orthonormal_iff_ite.1 b.orthonormal) i j
    rw [PiLp.inner_apply] at e
    rw [Matrix.one_apply, ← e]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.conjTranspose_apply, hQdef, hQdef, RCLike.inner_apply, Complex.star_def]
    ring
  have hQR : Q * R = Z := by
    ext a j
    rw [Matrix.mul_apply]
    have e := congrArg (fun v : EuclideanSpace ℂ (Fin N) => v.ofLp a) (b.sum_repr' (f j))
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      f, PiLp.toLp_apply, Matrix.col_apply] at e
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hQdef, hRdef]
    ring
  exact ⟨Q, triCoOf R, hQ, ht, by rw [hupR]; exact hQR⟩

theorem qrMap_image :
    qrMap '' (Set.univ ×ˢ triPos N) = {Z : Fin N → Fin N → ℂ | (Matrix.of Z).det ≠ 0} := by
  ext Z
  constructor
  · rintro ⟨⟨k, t⟩, ⟨-, ht⟩, rfl⟩
    show (toM k * upMat t).det ≠ 0
    rw [Matrix.det_mul]
    refine mul_ne_zero ?_ (qrA_upMat_det_ne t ht)
    intro h0
    have e := congrArg Matrix.det (qrA_unitary k)
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at e
    exact zero_ne_one e
  · intro hZ
    obtain ⟨Q, t, hQ, ht, hQt⟩ := qrA_exists (Matrix.of Z) hZ
    refine ⟨(⟨⟨Q, Qᴴ, mul_eq_one_comm.1 hQ, hQ⟩, ?_⟩, t), ⟨Set.mem_univ _, ht⟩, ?_⟩
    · show Qᴴ * Jm (fun _ : Fin N => true) * Q = Jm (fun _ : Fin N => true)
      rw [qrA_Jm_one, Matrix.mul_one]
      exact hQ
    · show Matrix.of.symm (Q * upMat t) = Z
      rw [hQt]
      rfl

end ReciprocityTheory.ChartRestriction.DS
