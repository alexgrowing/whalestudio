import Mathlib

open Matrix

namespace GlobalTheory

section SymplecticRatDense

variable {l : Type} [Fintype l] [DecidableEq l]

lemma exists_ratMatrix_iff {n : Type} (A : Matrix n n ℝ) :
    (∀ i j, ∃ q : ℚ, A i j = q) ↔ ∃ B : Matrix n n ℚ, B.map (Rat.castHom ℝ) = A := by
  constructor
  · intro h
    choose B hB using h
    exact ⟨Matrix.of B, by ext i j; simp [hB]⟩
  · rintro ⟨B, rfl⟩ i j
    exact ⟨B i j, by simp⟩

lemma map_ratCast_inv {n : Type} [Fintype n] [DecidableEq n] (B : Matrix n n ℚ) :
    (B⁻¹).map (Rat.castHom ℝ) = (B.map (Rat.castHom ℝ))⁻¹ := by
  have h1 := (Rat.castHom ℝ).map_det B
  have h2 := (Rat.castHom ℝ).map_adjugate B
  rw [RingHom.mapMatrix_apply] at h1 h2
  rw [RingHom.mapMatrix_apply] at h2
  rw [Matrix.inv_def, Matrix.inv_def, ← h1, ← h2]
  ext i j
  simp [Ring.inverse_eq_inv']

lemma denseRange_map_ratCast {n : Type} :
    DenseRange (fun B : Matrix n n ℚ => B.map (Rat.castHom ℝ)) := by
  have h : DenseRange (Pi.map (fun _ : n => Pi.map (fun _ : n => ((↑) : ℚ → ℝ)))) :=
    DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => Rat.denseRange_cast))
  exact h

lemma cayley_mem_symplecticGroup (X : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (hX : Xᵀ * J l ℝ + J l ℝ * X = 0) (hd : (1 + X).det ≠ 0) :
    (1 - X) * (1 + X)⁻¹ ∈ symplecticGroup l ℝ := by
  have hu : IsUnit (1 + X).det := isUnit_iff_ne_zero.2 hd
  rw [SymplecticGroup.mem_iff']
  have h1 : (1 - X)ᵀ * J l ℝ * (1 - X) = (1 + X)ᵀ * J l ℝ * (1 + X) := by
    have e : Xᵀ * J l ℝ = - (J l ℝ * X) := eq_neg_of_add_eq_zero_left hX
    simp only [transpose_sub, transpose_add, transpose_one, sub_mul, add_mul, mul_sub, mul_add,
      one_mul, mul_one, e]
    abel
  have h2 : (1 + X) * (1 + X)⁻¹ = 1 := mul_nonsing_inv _ hu
  calc ((1 - X) * (1 + X)⁻¹)ᵀ * J l ℝ * ((1 - X) * (1 + X)⁻¹)
      = ((1 + X)⁻¹)ᵀ * ((1 - X)ᵀ * J l ℝ * (1 - X)) * (1 + X)⁻¹ := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = ((1 + X) * (1 + X)⁻¹)ᵀ * J l ℝ * ((1 + X) * (1 + X)⁻¹) := by
        rw [h1]; simp only [transpose_mul, Matrix.mul_assoc]
    _ = J l ℝ := by rw [h2]; simp

lemma mem_closure_rat_symplectic_of_det (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (hγ : γ ∈ symplecticGroup l ℝ) (hd : (1 + γ).det ≠ 0) :
    γ ∈ closure {A : Matrix (l ⊕ l) (l ⊕ l) ℝ | A ∈ symplecticGroup l ℝ ∧
      ∃ B : Matrix (l ⊕ l) (l ⊕ l) ℚ, B.map (Rat.castHom ℝ) = A} := by
  have hu : IsUnit (1 + γ).det := isUnit_iff_ne_zero.2 hd
  set P := (1 + γ)⁻¹ with hP
  have hP1 : (1 + γ) * P = 1 := mul_nonsing_inv _ hu
  set X₀ := (1 - γ) * P with hX₀
  have hJ : J l ℝ * J l ℝ = -1 := J_squared l ℝ
  have hγ' : γᵀ * J l ℝ * γ = J l ℝ := SymplecticGroup.mem_iff'.1 hγ
  have hlie : X₀ᵀ * J l ℝ + J l ℝ * X₀ = 0 := by
    have h1 : (1 - γ)ᵀ * J l ℝ * (1 + γ) + (1 + γ)ᵀ * J l ℝ * (1 - γ) = 0 := by
      simp only [transpose_sub, transpose_add, transpose_one, sub_mul, add_mul, mul_sub, mul_add,
        one_mul, mul_one, hγ']
      abel
    calc X₀ᵀ * J l ℝ + J l ℝ * X₀
        = X₀ᵀ * J l ℝ * ((1 + γ) * P) + ((1 + γ) * P)ᵀ * J l ℝ * X₀ := by rw [hP1]; simp
      _ = Pᵀ * ((1 - γ)ᵀ * J l ℝ * (1 + γ) + (1 + γ)ᵀ * J l ℝ * (1 - γ)) * P := by
        rw [Matrix.mul_add Pᵀ, Matrix.add_mul (Pᵀ * _) _ P]
        simp only [hX₀, transpose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [h1]; simp
  have hplus : 1 + X₀ = (2 : ℝ) • P := by
    calc 1 + X₀ = (1 + γ) * P + (1 - γ) * P := by rw [hP1]
      _ = (2 : ℝ) • P := by
        simp only [add_mul, sub_mul, one_mul, two_smul]; abel
  have hminus : 1 - X₀ = γ * ((2 : ℝ) • P) := by
    calc 1 - X₀ = (1 + γ) * P - (1 - γ) * P := by rw [hP1]
      _ = γ * ((2 : ℝ) • P) := by
        simp only [add_mul, sub_mul, one_mul, two_smul, mul_add]; abel
  have hdet : (1 + X₀).det ≠ 0 := by
    rw [hplus, det_smul]
    refine mul_ne_zero (by positivity) ?_
    have := congrArg det hP1
    rw [det_mul, det_one] at this
    exact right_ne_zero_of_mul_eq_one this
  let Φ : Matrix (l ⊕ l) (l ⊕ l) ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ :=
    fun T => -(J l ℝ * (T + Tᵀ))
  have hΦ : Continuous Φ := by
    refine (Continuous.matrix_mul continuous_const (continuous_id.add ?_)).neg
    exact continuous_id.matrix_transpose
  let T₀ : Matrix (l ⊕ l) (l ⊕ l) ℝ := (1 / 2 : ℝ) • (J l ℝ * X₀)
  have hT₀ : Φ T₀ = X₀ := by
    have e : X₀ᵀ * J l ℝ = - (J l ℝ * X₀) := eq_neg_of_add_eq_zero_left hlie
    have e2 : T₀ᵀ = T₀ := by
      simp only [T₀, transpose_smul, transpose_mul, J_transpose, Matrix.mul_neg, e, neg_neg]
    have e3 : T₀ + T₀ = J l ℝ * X₀ := by
      simp only [T₀, ← add_smul]; norm_num
    simp only [Φ, e2, e3, ← Matrix.mul_assoc, hJ]; simp
  have hΦlie : ∀ T, (Φ T)ᵀ * J l ℝ + J l ℝ * Φ T = 0 := by
    intro T
    simp only [Φ, transpose_neg, transpose_mul, transpose_add, transpose_transpose, J_transpose,
      Matrix.mul_neg, neg_neg, Matrix.mul_assoc, hJ]
    simp only [← Matrix.mul_assoc, hJ]
    simp only [Matrix.mul_neg, Matrix.neg_mul, mul_one, one_mul, neg_neg]
    abel
  let U : Set (Matrix (l ⊕ l) (l ⊕ l) ℝ) := {T | (1 + Φ T).det ≠ 0}
  have hU : IsOpen U :=
    isOpen_ne_fun (continuous_const.add hΦ).matrix_det continuous_const
  have hT₀U : T₀ ∈ U := by simpa [U, hT₀] using hdet
  have hcl := (denseRange_map_ratCast (n := l ⊕ l)).open_subset_closure_inter hU hT₀U
  let F : Matrix (l ⊕ l) (l ⊕ l) ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ :=
    fun T => (1 - Φ T) * (1 + Φ T)⁻¹
  have hF : ContinuousAt F T₀ := by
    have h1 : ContinuousAt (fun T => (1 + Φ T)⁻¹) T₀ := by
      refine ContinuousAt.comp (f := fun T => 1 + Φ T) (continuousAt_matrix_inv _ ?_)
        (continuous_const.add hΦ).continuousAt
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hT₀U
    exact (continuous_const.sub hΦ).continuousAt.mul h1
  have hF₀ : F T₀ = γ := by
    simp only [F, hT₀]
    rw [hminus, ← hplus, Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), mul_one]
  rw [← hF₀]
  refine hF.continuousWithinAt.mem_closure hcl ?_
  rintro T ⟨hT, B, rfl⟩
  refine ⟨cayley_mem_symplecticGroup _ (hΦlie _) hT, ?_⟩
  refine ⟨(1 - -(J l ℚ * (B + Bᵀ))) * (1 + -(J l ℚ * (B + Bᵀ)))⁻¹, ?_⟩
  have hm : (-(J l ℚ * (B + Bᵀ))).map (Rat.castHom ℝ) = Φ (B.map (Rat.castHom ℝ)) := by
    simp only [Φ]
    rw [Matrix.map_neg _ (map_neg _), Matrix.map_mul, Matrix.map_add _ (map_add _), transpose_map, map_J]
  simp only [F]
  rw [Matrix.map_mul, map_ratCast_inv, Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), hm,
    Matrix.map_one _ (map_zero _) (map_one _)]

lemma det_complex_ne_zero_of_symplectic (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (hγ : γ ∈ symplecticGroup l ℝ) :
    ((1 + γ).map Complex.ofRealHom + Complex.I • (J l ℝ * (1 - γ)).map Complex.ofRealHom).det
      ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  set G := γ.map Complex.ofRealHom with hG
  have hJ : J l ℂ * J l ℂ = -1 := J_squared l ℂ
  have hγ' : Gᴴ * J l ℂ * G = J l ℂ := by
    have h := congrArg (fun A => A.map Complex.ofRealHom) (SymplecticGroup.mem_iff'.1 hγ)
    simp only [Matrix.map_mul, map_J] at h
    have : Gᴴ = γᵀ.map Complex.ofRealHom := by ext i j; simp [hG]
    rw [this]; exact h
  rw [Matrix.map_mul, map_J, Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _),
    Matrix.map_one _ (map_zero _) (map_one _), ← hG] at hz
  set w := G *ᵥ v with hw
  have hJJ : ∀ x : l ⊕ l → ℂ, J l ℂ *ᵥ (J l ℂ *ᵥ x) = -x := by
    intro x; rw [mulVec_mulVec, hJ, neg_mulVec, one_mulVec]
  have e1 : v + w + Complex.I • (J l ℂ *ᵥ v - J l ℂ *ᵥ w) = 0 := by
    rw [← hz, add_mulVec, add_mulVec, one_mulVec, smul_mulVec, ← mulVec_mulVec, sub_mulVec,
      one_mulVec, mulVec_sub]
  have e2 : J l ℂ *ᵥ v + J l ℂ *ᵥ w + Complex.I • (w - v) = 0 := by
    have := congrArg (fun x => J l ℂ *ᵥ x) e1
    simp only [mulVec_add, mulVec_smul, mulVec_sub, hJJ, mulVec_zero] at this
    rw [← this]; congr 2; abel
  have ev : J l ℂ *ᵥ v = Complex.I • v := by
    ext i
    have a := congrFun e1 i
    have b := congrFun e2 i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at a b ⊢
    linear_combination (1 / 2 : ℂ) * b - (Complex.I / 2) * a +
      (1 / 2 : ℂ) * ((J l ℂ *ᵥ v) i - (J l ℂ *ᵥ w) i) * Complex.I_mul_I
  have ew : J l ℂ *ᵥ w = -Complex.I • w := by
    ext i
    have a := congrFun e1 i
    have b := congrFun e2 i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at a b ⊢
    linear_combination (1 / 2 : ℂ) * b + (Complex.I / 2) * a -
      (1 / 2 : ℂ) * ((J l ℂ *ᵥ v) i - (J l ℂ *ᵥ w) i) * Complex.I_mul_I
  have key : star w ⬝ᵥ (J l ℂ *ᵥ w) = star v ⬝ᵥ (J l ℂ *ᵥ v) := by
    conv_rhs => rw [← hγ']
    rw [hw, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  rw [ev, ew, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at key
  have key2 : star v ⬝ᵥ v + star w ⬝ᵥ w = 0 := by
    linear_combination Complex.I * key + (star v ⬝ᵥ v + star w ⬝ᵥ w) * Complex.I_mul_I
  open ComplexOrder in
  have := (add_eq_zero_iff_of_nonneg (dotProduct_star_self_nonneg v)
    (dotProduct_star_self_nonneg w)).1 key2
  open ComplexOrder in
  exact hv (dotProduct_star_self_eq_zero.1 this.1)

lemma exists_rat_det_ne_zero_of_symplectic (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (hγ : γ ∈ symplecticGroup l ℝ) :
    ∃ t : ℚ, ((1 + γ) + (t : ℝ) • (J l ℝ * (1 - γ))).det ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  set A := 1 + γ with hA
  set B := J l ℝ * (1 - γ) with hB
  let p : Polynomial ℝ :=
    (A.map Polynomial.C + (Polynomial.X : Polynomial ℝ) • B.map Polynomial.C).det
  have hp : p = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot p
      ((Set.infinite_range_of_injective (Rat.cast_injective (α := ℝ))).mono ?_)
    rintro _ ⟨t, rfl⟩
    have h := (Polynomial.evalRingHom (t : ℝ)).map_det
      (A.map Polynomial.C + (Polynomial.X : Polynomial ℝ) • B.map Polynomial.C)
    change Polynomial.evalRingHom (t : ℝ) p = 0
    rw [h, ← hcon t]
    congr 1
    ext i j
    simp
    exact mul_comm _ _
  apply det_complex_ne_zero_of_symplectic γ hγ
  have h := (Polynomial.eval₂RingHom Complex.ofRealHom Complex.I).map_det
      (A.map Polynomial.C + (Polynomial.X : Polynomial ℝ) • B.map Polynomial.C)
  change Polynomial.eval₂RingHom Complex.ofRealHom Complex.I p = _ at h
  rw [hp, map_zero] at h
  rw [h]
  congr 1
  ext i j
  simp [← hA, ← hB]
  exact mul_comm _ _

theorem dense_rat_symplecticGroup :
    Dense {γ : Matrix.symplecticGroup l ℝ |
      ∀ i j, ∃ q : ℚ, (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ) i j = q} := by
  rintro ⟨γ, hγ⟩
  obtain ⟨t, ht⟩ := exists_rat_det_ne_zero_of_symplectic γ hγ
  have hJ : J l ℝ * J l ℝ = -1 := J_squared l ℝ
  set X : Matrix (l ⊕ l) (l ⊕ l) ℝ := -((t : ℝ) • J l ℝ) with hX
  have hXlie : Xᵀ * J l ℝ + J l ℝ * X = 0 := by simp [hX, hJ]
  have hXd : (1 + X).det ≠ 0 := by
    have : (1 + X) * (1 - X) = (1 + (t : ℝ) ^ 2) • 1 := by
      simp only [hX, add_mul, mul_sub, one_mul, mul_one, Matrix.neg_mul, Matrix.mul_neg, neg_neg,
        Matrix.smul_mul, Matrix.mul_smul, hJ, add_smul, one_smul, smul_smul, smul_neg, sq]
      abel
    have h2 := congrArg det this
    rw [det_mul, det_smul, det_one, mul_one] at h2
    refine left_ne_zero_of_mul (b := (1 - X).det) ?_
    rw [h2]
    positivity
  have hXu : IsUnit (1 + X).det := isUnit_iff_ne_zero.2 hXd
  let δ : symplecticGroup l ℝ := ⟨_, cayley_mem_symplecticGroup X hXlie hXd⟩
  have hδ : (1 + X) * δ.1 = 1 - X := by
    have c : (1 + X) * (1 - X) = (1 - X) * (1 + X) := by noncomm_ring
    change (1 + X) * ((1 - X) * (1 + X)⁻¹) = _
    rw [← Matrix.mul_assoc, c, Matrix.mul_assoc, mul_nonsing_inv _ hXu, mul_one]
  let γ' : symplecticGroup l ℝ := δ⁻¹ * ⟨γ, hγ⟩
  have hγ' : δ.1 * γ'.1 = γ := by
    have : δ * γ' = ⟨γ, hγ⟩ := by simp [γ']
    exact congrArg Subtype.val this
  have hd : (1 + γ'.1).det ≠ 0 := by
    have : (1 + X) * δ.1 * (1 + γ'.1) = (1 + γ) + (t : ℝ) • (J l ℝ * (1 - γ)) := by
      rw [mul_add, mul_one, Matrix.mul_assoc, hγ', hδ]
      simp only [hX, add_mul, mul_sub, one_mul, mul_one, Matrix.neg_mul, Matrix.smul_mul, smul_sub]
      abel
    rw [← this, det_mul] at ht
    exact right_ne_zero_of_mul ht
  have hcl := mem_closure_rat_symplectic_of_det γ'.1 γ'.2 hd
  rw [closure_subtype]
  change γ ∈ _
  rw [← hγ']
  have hc : Continuous (fun A : Matrix (l ⊕ l) (l ⊕ l) ℝ => δ.1 * A) :=
    continuous_const.mul continuous_id
  refine hc.continuousWithinAt.mem_closure hcl ?_
  rintro A ⟨hA, B, rfl⟩
  refine ⟨⟨_, mul_mem δ.2 hA⟩, (exists_ratMatrix_iff _).2 ?_, rfl⟩
  refine ⟨(1 - -(t • J l ℚ)) * (1 + -(t • J l ℚ))⁻¹ * B, ?_⟩
  have hm : (-(t • J l ℚ)).map (Rat.castHom ℝ) = X := by
    rw [hX, ← map_J l (Rat.castHom ℝ)]
    ext i j; simp
  rw [Matrix.map_mul, Matrix.map_mul, map_ratCast_inv, Matrix.map_sub _ (map_sub _),
    Matrix.map_add _ (map_add _), hm, Matrix.map_one _ (map_zero _) (map_one _)]

end SymplecticRatDense

theorem dense_rat_symplecticGroup_fin : ∀ g : ℕ, Dense {γ : Matrix.symplecticGroup (Fin g) ℝ |
    ∀ i j, ∃ q : ℚ, (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) i j = q} :=
  fun _ => dense_rat_symplecticGroup

end GlobalTheory
