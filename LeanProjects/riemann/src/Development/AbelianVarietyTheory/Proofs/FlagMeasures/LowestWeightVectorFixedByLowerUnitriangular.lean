import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition

open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Dec.LowFix

variable {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

lemma exists_deriv (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W))
    (h : DifferentiableAt ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y))
      (fun i j => (1 : Matrix (Fin n) (Fin n) ℂ) i j)) :
    ∃ D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (W →L[ℂ] W), ∀ N v,
      HasDerivAt (fun z : ℂ => τ (1 + z • N) v) (D N v) 0 := by
  set F : (Fin n → Fin n → ℂ) → (W →L[ℂ] W) := fun y => τ (Matrix.of y) with hF
  set p : Fin n → Fin n → ℂ := fun i j => (1 : Matrix (Fin n) (Fin n) ℂ) i j with hp
  refine ⟨(fderiv ℂ F p).toLinearMap ∘ₗ (Matrix.ofLinearEquiv ℂ).symm.toLinearMap, fun N v => ?_⟩
  have hg : HasDerivAt (fun z : ℂ => p + z • (Matrix.ofLinearEquiv ℂ).symm N)
      ((Matrix.ofLinearEquiv ℂ).symm N) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const ((Matrix.ofLinearEquiv ℂ).symm N)).const_add p
  have h0 : HasFDerivAt F (fderiv ℂ F p) (p + (0 : ℂ) • (Matrix.ofLinearEquiv ℂ).symm N) := by
    rw [zero_smul, add_zero]
    exact h.hasFDerivAt
  have h1 := h0.comp_hasDerivAt (0 : ℂ) hg
  exact (ContinuousLinearMap.apply ℂ W v).hasFDerivAt.comp_hasDerivAt (0 : ℂ) h1

def Nil (ε : Fin n → Bool) (N : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i j, i ≤ j → N i j = 0) ∧ N * Jm ε = Jm ε * N

lemma one_add_det {N : Matrix (Fin n) (Fin n) ℂ} (hN : ∀ i j, i ≤ j → N i j = 0) (z : ℂ) :
    (1 + z • N).det = 1 := by
  have hT : (1 + z • N).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp [Matrix.one_apply_ne hij'.ne, hN i j hij'.le]
  rw [Matrix.det_of_lowerTriangular _ hT]
  exact Finset.prod_eq_one fun i _ => by simp [hN i i le_rfl]

lemma one_add_mem {ε : Fin n → Bool} {N : Matrix (Fin n) (Fin n) ℂ} (hN : Nil ε N) (z : ℂ) :
    1 + z • N ∈ KC ε := by
  obtain ⟨hN1, hN2⟩ := id hN
  simp only [KC, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, one_add_det hN1 z]
    exact isUnit_one
  · rw [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hN2]

lemma nil_single {ε : Fin n → Bool} {a b : Fin n} (hab : b < a) (he : ε a = ε b) :
    Nil ε (Matrix.single a b (1 : ℂ)) := by
  unfold Nil
  refine ⟨fun i j hij => ?_, ?_⟩
  · by_cases hi : i = a
    · subst hi
      have hj : j ≠ b := fun hj => absurd (hj ▸ hij) (not_le.mpr hab)
      simp [Matrix.single_apply, hj, Ne.symm hj]
    · simp [Matrix.single_apply, hi, Ne.symm hi]
  · ext i j
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : i = a
    · by_cases hj : j = b
      · subst hi hj
        simp [Matrix.single_apply, he]
      · simp [Matrix.single_apply, hj, Ne.symm hj]
    · simp [Matrix.single_apply, hi, Ne.symm hi]

private lemma sum_mul_root_eq_sub_flag_measures (x y : Fin n) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * root x y i = ((x : ℕ) : ℝ) - ((y : ℕ) : ℝ) := by
  simp [root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

lemma not_cdom {ε : Fin n → Bool} {a b : Fin n} (hab : b < a) (abelian₂ : Fin n → ℝ) :
    ¬ CDom ε (abelian₂ - root a b) abelian₂ := by
  rintro ⟨c, hc, hsum⟩
  rw [sub_sub_cancel] at hsum
  have key := congrArg (fun v : Fin n → ℝ => ∑ i : Fin n, ((i : ℕ) : ℝ) * v i) hsum
  rw [sum_mul_root_eq_sub_flag_measures] at key
  have hr : ∑ i : Fin n, ((i : ℕ) : ℝ) * (∑ x, ∑ y, (c x y : ℝ) • root x y) i
      = ∑ x, ∑ y, (c x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← sum_mul_root_eq_sub_flag_measures x y, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hr] at key
  have hle : ∑ x, ∑ y, (c x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) ≤ 0 := by
    refine Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y _ => ?_
    by_cases h0 : c x y = 0
    · simp [h0]
    · have hxy : (x : ℕ) < y := (hc x y h0).1
      have hxy' : ((x : ℕ) : ℝ) < ((y : ℕ) : ℝ) := by exact_mod_cast hxy
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hab0 : (b : ℕ) < a := hab
  have hab' : ((b : ℕ) : ℝ) < ((a : ℕ) : ℝ) := by exact_mod_cast hab0
  linarith

lemma wt_single {ε : Fin n → Bool} {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)}
    (hτ : IsCRepOn (KC ε) τ) {D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (W →L[ℂ] W)}
    (hD : ∀ N v, HasDerivAt (fun z : ℂ => τ (1 + z • N) v) (D N v) 0)
    {abelian₂ : Fin n → ℝ} {w : W} (hw : IsWtOn (Kset ε) τ (-abelian₂) w)
    {a b : Fin n} (hab : b < a) (he : ε a = ε b) :
    IsWtOn (Kset ε) τ (-(abelian₂ - root a b)) (D (Matrix.single a b 1) w) := by
  obtain ⟨_, hτ2⟩ := id hτ
  intro θ hθ
  obtain ⟨_, hθJ⟩ := id hθ
  have htw := hw θ hθ
  set t := Matrix.diagonal (fun i => Complex.exp ((θ i : ℂ) * Complex.I)) with ht
  set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1 with hE
  set κ : ℂ := Complex.exp (((θ a - θ b : ℝ) : ℂ) * Complex.I) with hκ
  set c : ℂ := Complex.exp (((∑ i, (-abelian₂) i * θ i : ℝ) : ℂ) * Complex.I) with hc
  have hL : ∀ i j, (t * E) i j = Complex.exp ((θ a : ℂ) * Complex.I) * E i j := by
    intro i j
    rw [ht, Matrix.diagonal_mul]
    by_cases hi : i = a
    · rw [hi]
    · simp [hE, Matrix.single_apply, hi, Ne.symm hi]
  have hR : ∀ i j, (E * t) i j = E i j * Complex.exp ((θ b : ℂ) * Complex.I) := by
    intro i j
    rw [ht, Matrix.mul_diagonal]
    by_cases hj : j = b
    · rw [hj]
    · simp [hE, Matrix.single_apply, hj, Ne.symm hj]
  have hk : Complex.exp ((θ a : ℂ) * Complex.I) = κ * Complex.exp ((θ b : ℂ) * Complex.I) := by
    rw [hκ, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hcomm : ∀ z : ℂ, t * (1 + z • E) = (1 + (κ * z) • E) * t := by
    intro z
    rw [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hL, hR, hk]
    ring
  have hmem : ∀ z : ℂ, 1 + z • E ∈ KC ε := fun z => one_add_mem (nil_single hab he) z
  have htK : t ∈ KC ε := by
    simp only [KC, Set.mem_setOf_eq]
    refine ⟨?_, hθJ⟩
    rw [Matrix.isUnit_iff_isUnit_det, ht, Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => Complex.exp_ne_zero _)
  have hfun : ∀ z : ℂ, τ t (τ (1 + z • E) w) = c • τ (1 + (κ * z) • E) w := by
    intro z
    rw [← ContinuousLinearMap.comp_apply, ← hτ2 _ htK _ (hmem z), hcomm z, hτ2 _ (hmem _) _ htK,
      ContinuousLinearMap.comp_apply, htw, map_smul]
  have hD0 : HasDerivAt (fun z : ℂ => τ (1 + z • E) w) (D E w) (κ * 0) := by
    rw [mul_zero]
    exact hD E w
  have hk' : HasDerivAt (fun z : ℂ => κ * z) κ 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul κ
  have h2 := (HasDerivAt.scomp (h := fun z : ℂ => κ * z) 0 hD0 hk').const_smul c
  have h1 := (τ t).hasFDerivAt.comp_hasDerivAt (0 : ℂ) (hD E w)
  have h1' : HasDerivAt (fun y => c • ((fun z : ℂ => τ (1 + z • E) w) ∘ fun z => κ * z) y)
      (τ t (D E w)) 0 :=
    h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => by
      simp only [Function.comp_apply]
      exact (hfun z).symm)
  have key := h1'.unique h2
  have hr : ∑ i, root a b i * θ i = θ a - θ b := by
    simp [root, sub_mul, Finset.sum_sub_distrib, Pi.single_apply]
  have hs : ∑ i, (-(abelian₂ - root a b)) i * θ i = ∑ i, (-abelian₂) i * θ i + (θ a - θ b) := by
    rw [← hr, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.neg_apply, Pi.sub_apply]
    ring
  rw [key, smul_smul]
  congr 1
  rw [hc, hκ, ← Complex.exp_add, hs]
  congr 1
  push_cast
  ring

private lemma pi_single_eq_re_smul_add_im_smul (i j : Fin n) (x : ℂ) :
    Matrix.single i j x = x • Matrix.single i j (1 : ℂ) := by
  ext k l
  simp [Matrix.single_apply]

lemma deriv_nil {ε : Fin n → Bool} {D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (W →L[ℂ] W)} {w : W}
    (h : ∀ a b, b < a → ε a = ε b → D (Matrix.single a b 1) w = 0)
    {N : Matrix (Fin n) (Fin n) ℂ} (hN : Nil ε N) : D N w = 0 := by
  obtain ⟨hN1, hN2⟩ := id hN
  rw [Matrix.matrix_eq_sum_single N]
  simp only [map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [pi_single_eq_re_smul_add_im_smul, map_smul, ContinuousLinearMap.smul_apply]
  by_cases h0 : N i j = 0
  · rw [h0, zero_smul]
  · have hji : j < i := not_le.mp fun hle => h0 (hN1 i j hle)
    have he : ε i = ε j := by
      have hc := congrFun (congrFun hN2 i) j
      simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at hc
      by_contra hne
      apply h0
      have hd : (if ε j then (1 : ℂ) else -1) = -(if ε i then (1 : ℂ) else -1) := by
        cases hi : ε i <;> cases hj : ε j <;> simp_all
      rw [hd] at hc
      have h2 : (2 : ℂ) * (if ε i then (1 : ℂ) else -1) * N i j = 0 := by linear_combination -hc
      have hs0 : (if ε i then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 (mul_ne_zero two_ne_zero hs0)
      · exact h3
    rw [h i j hji he, smul_zero]

lemma nil_inv_mul {ε : Fin n → Bool} {N : Matrix (Fin n) (Fin n) ℂ} (hN : Nil ε N) (s : ℂ) :
    Nil ε ((1 + s • N)⁻¹ * N) := by
  obtain ⟨hN1, _⟩ := id hN
  set A := 1 + s • N with hA
  have hu : IsUnit A.det := by
    rw [hA, one_add_det hN1 s]
    exact isUnit_one
  obtain ⟨_, hAJ⟩ := id (one_add_mem hN s)
  have hT : A.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp [hA, Matrix.one_apply_ne hij'.ne, hN1 i j hij'.le]
  haveI : Invertible A := Matrix.invertibleOfIsUnitDet A hu
  have hTi : A⁻¹.BlockTriangular OrderDual.toDual := Matrix.blockTriangular_inv_of_blockTriangular hT
  unfold Nil
  refine ⟨fun i j hij => ?_, ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : i < k
    · rw [hTi (OrderDual.toDual_lt_toDual.mpr hk), zero_mul]
    · rw [hN1 k j (le_trans (not_lt.mp hk) hij), mul_zero]
  · have hiJ : A⁻¹ * Jm ε = Jm ε * A⁻¹ := by
      calc A⁻¹ * Jm ε = A⁻¹ * Jm ε * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv _ hu, mul_one]
        _ = A⁻¹ * (Jm ε * A) * A⁻¹ := by simp only [mul_assoc]
        _ = A⁻¹ * (A * Jm ε) * A⁻¹ := by rw [hAJ]
        _ = Jm ε * A⁻¹ := by rw [← mul_assoc, Matrix.nonsing_inv_mul _ hu, one_mul]
    obtain ⟨_, hN2⟩ := id hN
    rw [mul_assoc, hN2, ← mul_assoc, hiJ, mul_assoc]

theorem lowest_fixed : ∀ (n : ℕ) (ε : Fin n → Bool) (abelian₂ : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), Formalism.QuantumDeterminants.IsCRepOn (GlobalTheory.Dec.KC ε) τ → DifferentiableAt ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) (fun i j => (1 : Matrix (Fin n) (Fin n) ℂ) i j) → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) τ (-abelian₂) w → (∀ (μ : Fin n → ℝ) (v : W), v ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) τ (-μ) v → Formalism.MainNotions.S.CDom ε μ abelian₂) → ∀ y ∈ GlobalTheory.Dec.KC ε, Formalism.MainNotions.S.IsLoUni y → τ y w = w := by
  intro n ε abelian₂ W _ _ τ w hτ hdiff hw hlow y hy hyL
  obtain ⟨hτ1, hτ2⟩ := id hτ
  obtain ⟨D, hD⟩ := exists_deriv τ hdiff
  have hE : ∀ a b : Fin n, b < a → ε a = ε b → D (Matrix.single a b 1) w = 0 := by
    intro a b hab he
    by_contra hne
    exact not_cdom hab abelian₂ (hlow _ _ hne (wt_single hτ hD hw hab he))
  set N := y - 1 with hNdef
  have hyN : y = 1 + N := by rw [hNdef, add_sub_cancel]
  obtain ⟨_, hyJ⟩ := id hy
  have hNil : Nil ε N := by
    unfold Nil
    refine ⟨fun i j hij => ?_, ?_⟩
    · rcases lt_or_eq_of_le hij with h | h
      · simp [hNdef, (hyL i j).1 h, Matrix.one_apply_ne h.ne]
      · subst h
        simp [hNdef, (hyL i i).2 rfl]
    · rw [hNdef, sub_mul, mul_sub, one_mul, mul_one, hyJ]
  obtain ⟨hNil1, _⟩ := id hNil
  have hderiv : ∀ s : ℂ, HasDerivAt (fun u : ℂ => τ (1 + u • N) w) 0 s := by
    intro s
    set A := 1 + s • N with hA
    have hdet : IsUnit A.det := by
      rw [hA, one_add_det hNil1 s]
      exact isUnit_one
    set M := A⁻¹ * N with hM
    have hMN : Nil ε M := nil_inv_mul hNil s
    have hAmem : A ∈ KC ε := one_add_mem hNil s
    have hfac : ∀ u : ℂ, 1 + u • N = A * (1 + (u - s) • M) := by
      intro u
      rw [mul_add, mul_one, hM, mul_smul_comm, ← mul_assoc, Matrix.mul_nonsing_inv _ hdet, one_mul, hA,
        add_assoc, ← add_smul, add_sub_cancel]
    have hM0 : HasDerivAt (fun h : ℂ => τ (1 + h • M) w) 0 (s - s) := by
      rw [sub_self, ← deriv_nil hE hMN]
      exact hD M w
    have hsh : HasDerivAt (fun u : ℂ => u - s) 1 s := (hasDerivAt_id s).sub_const s
    have hc2 := (τ A).hasFDerivAt.comp_hasDerivAt s (HasDerivAt.scomp (h := fun u : ℂ => u - s) s hM0 hsh)
    rw [smul_zero, map_zero] at hc2
    refine hc2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    simp only [Function.comp_apply]
    rw [hfac u, hτ2 _ hAmem _ (one_add_mem hMN _), ContinuousLinearMap.comp_apply]
  have hconst : (fun u : ℂ => τ (1 + u • N) w) 1 = (fun u : ℂ => τ (1 + u • N) w) 0 :=
    is_const_of_deriv_eq_zero (by intro s; exact (hderiv s).differentiableAt)
      (fun s => (hderiv s).deriv) 1 0
  simp only [one_smul, zero_smul, add_zero] at hconst
  rw [hyN, hconst, hτ1, ContinuousLinearMap.one_apply]

end GlobalTheory.Dec.LowFix
