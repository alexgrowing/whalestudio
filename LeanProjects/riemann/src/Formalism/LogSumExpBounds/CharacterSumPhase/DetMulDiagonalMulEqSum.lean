import Formalism.LogSumExpBounds.NuclearBound

namespace Formalism.NuclearRankWeightBounds.P

open Matrix Polynomial Finset

theorem det_mul_diagonal_mul_eq_sum {R : Type*} [CommRing R] {n : Type*} [Fintype n]
    [DecidableEq n] {k : ℕ} (A : Matrix (Fin k) n R) (B : Matrix n (Fin k) R) (d : n → R) :
    (A * diagonal d * B).det =
      ∑ J ∈ powersetCard k (univ : Finset n),
        (∏ j ∈ J, d j) * ((B * A).submatrix (Subtype.val : J → n) Subtype.val).det := by
  have h := Matrix.det_one_add_mul_comm ((X : R[X]) • (A.map C)) ((diagonal d * B).map C)
  have e1 : (X : R[X]) • A.map C * (diagonal d * B).map C
      = (X : R[X]) • (A * diagonal d * B).map C := by
    rw [Matrix.smul_mul, ← Matrix.map_mul, Matrix.mul_assoc]
  have e2 : (diagonal d * B).map C * ((X : R[X]) • A.map C)
      = (X : R[X]) • (diagonal d * (B * A)).map C := by
    rw [Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_assoc]
  rw [e1, e2] at h
  have h2 := congrArg (fun p => Polynomial.coeff p k) h
  simp only [coeff_det_one_add_X_smul_eq_sum_minors] at h2
  have hu : powersetCard k (univ : Finset (Fin k)) = {univ} := by
    simpa using Finset.powersetCard_self (univ : Finset (Fin k))
  rw [hu, sum_singleton] at h2
  rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (fun x => mem_univ x))]
  refine h2.trans (sum_congr rfl fun J _ => ?_)
  have : (diagonal d * (B * A)).submatrix (fun x : J => (x : n)) (fun x : J => (x : n))
      = diagonal (fun x : J => d x) * (B * A).submatrix (fun x : J => (x : n)) (fun x : J => (x : n)) := by
    ext a b; simp [diagonal_mul]
  rw [this, det_mul, det_diagonal, Finset.prod_coe_sort J d]

theorem coeff_prod_one_add {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι] (f : ι → R)
    (J : Finset ι) :
    (∏ j ∈ J, (1 + X * C (f j))).coeff 0 = 1 ∧
    (∏ j ∈ J, (1 + X * C (f j))).coeff 1 = ∑ j ∈ J, f j ∧
    2 * (∏ j ∈ J, (1 + X * C (f j))).coeff 2 = (∑ j ∈ J, f j) ^ 2 - ∑ j ∈ J, f j ^ 2 := by
  induction J using Finset.induction_on with
  | empty => simp [coeff_one]
  | insert a J ha ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    rw [prod_insert ha, sum_insert ha, sum_insert ha]
    set P := ∏ j ∈ J, (1 + X * C (f j))
    have key : (1 + X * C (f a)) * P = P + X * (C (f a) * P) := by ring
    rw [key]
    refine ⟨?_, ?_, ?_⟩
    · simp [coeff_add, h0]
    · rw [coeff_add, coeff_X_mul, coeff_C_mul, h0, h1]; ring
    · rw [coeff_add, coeff_X_mul, coeff_C_mul, h1]; linear_combination h2

theorem moment {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ} (A : Matrix (Fin k) n ℂ)
    (hA : A * Aᴴ = 1) (ν : n → ℂ) (m : ℕ) :
    ∑ J ∈ powersetCard k (univ : Finset n),
      (∏ j ∈ J, (1 + X * C (ν j))).coeff m *
        ((Aᴴ * A).submatrix (fun x : J => (x : n)) (fun x : J => (x : n))).det
    = (det (1 + (X : ℂ[X]) • (A * diagonal ν * Aᴴ).map C)).coeff m := by
  have h := det_mul_diagonal_mul_eq_sum (A.map C) (Aᴴ.map C) (fun j => 1 + X * C (ν j))
  have hd : diagonal (fun j => (1 : ℂ[X]) + X * C (ν j)) = 1 + (X : ℂ[X]) • (diagonal ν).map C := by
    ext a b; by_cases hab : a = b <;> simp [diagonal, one_apply, hab]
  have h1 : A.map C * Aᴴ.map C = 1 := by rw [← Matrix.map_mul, hA]; simp
  have h3 : A.map C * (diagonal ν).map C * Aᴴ.map C = (A * diagonal ν * Aᴴ).map C := by
    rw [Matrix.map_mul, Matrix.map_mul]
  have e : A.map C * diagonal (fun j => 1 + X * C (ν j)) * Aᴴ.map C
      = 1 + (X : ℂ[X]) • (A * diagonal ν * Aᴴ).map C := by
    rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1, Matrix.mul_smul, Matrix.smul_mul, h3]
  rw [e] at h
  rw [h, finsetSum_coeff]
  refine sum_congr rfl fun J _ => ?_
  have hs : (Aᴴ.map C * A.map C).submatrix (fun x : J => (x : n)) (fun x : J => (x : n))
      = ((Aᴴ * A).submatrix (fun x : J => (x : n)) (fun x : J => (x : n))).map C := by
    rw [← Matrix.map_mul]; rfl
  have hdet : (((Aᴴ * A).submatrix (fun x : J => (x : n)) (fun x : J => (x : n))).map C).det
      = C ((Aᴴ * A).submatrix (fun x : J => (x : n)) (fun x : J => (x : n))).det := by
    rw [RingHom.map_det]; rfl
  rw [hs, hdet, coeff_mul_C]

theorem two_coeff_two_det {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (hM : M.IsHermitian) :
    2 * (det (1 + (X : ℂ[X]) • M.map C)).coeff 2 = (trace M) ^ 2 - trace (M * M) := by
  set V : Matrix (Fin k) (Fin k) ℂ := (hM.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) with hVdef
  set L : Fin k → ℂ := RCLike.ofReal ∘ hM.eigenvalues with hLdef
  have hVV : V * Vᴴ = 1 := by
    simpa [V, star_eq_conjTranspose] using Unitary.coe_mul_star_self hM.eigenvectorUnitary
  have hVV' : Vᴴ * V = 1 := by
    simpa [V, star_eq_conjTranspose] using Unitary.coe_star_mul_self hM.eigenvectorUnitary
  have hspec : M = V * diagonal L * Vᴴ := by
    conv_lhs => rw [hM.spectral_theorem]
    simp [V, L, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  have hMM : M * M = V * diagonal (fun a => L a * L a) * Vᴴ := by
    rw [hspec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V, hVV', Matrix.one_mul, ← Matrix.mul_assoc (diagonal L) (diagonal L),
      diagonal_mul_diagonal]
  have hu : powersetCard k (univ : Finset (Fin k)) = {univ} := by
    simpa using Finset.powersetCard_self (univ : Finset (Fin k))
  have hone : ((Vᴴ * V).submatrix (fun x : (univ : Finset (Fin k)) => (x : Fin k))
      (fun x : (univ : Finset (Fin k)) => (x : Fin k))).det = 1 := by
    rw [hVV']
    exact (Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (fun x => mem_univ x)) 1).trans
      det_one
  have single : ∀ (ν : Fin k → ℂ) (m : ℕ),
      (det (1 + (X : ℂ[X]) • (V * diagonal ν * Vᴴ).map C)).coeff m
        = (∏ j ∈ (univ : Finset (Fin k)), (1 + X * C (ν j))).coeff m := by
    intro ν m
    rw [← moment V hVV ν m, hu, sum_singleton, hone, mul_one]
  have htr : trace M = ∑ j, L j := by
    rw [← coeff_det_one_add_X_smul_one, hspec, single, (coeff_prod_one_add L univ).2.1]
  have htr2 : trace (M * M) = ∑ j, L j ^ 2 := by
    rw [← coeff_det_one_add_X_smul_one, hMM, single,
      (coeff_prod_one_add (fun a => L a * L a) univ).2.1]
    simp [pow_two]
  rw [htr, htr2, hspec, single, (coeff_prod_one_add L univ).2.2]

theorem sum_castLE_eq {N i : ℕ} (hi : i ≤ N) {β : Type*} [AddCommMonoid β] (f : Fin N → β) :
    ∑ a : Fin i, f (Fin.castLE hi a) = ∑ a ∈ univ.filter (fun a : Fin N => a.val < i), f a := by
  refine Finset.sum_bij' (fun a _ => Fin.castLE hi a) (fun a ha => ⟨a.val, (mem_filter.mp ha).2⟩)
    ?_ ?_ ?_ ?_ ?_ <;> intros <;> simp_all

open scoped ComplexOrder in
theorem cb_weights : Formalism.NuclearRankWeightBounds.D.CBWeights := by
  intro N Y hY i hi
  set U : Matrix (Fin N) (Fin N) ℂ := (hY.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hUdef
  set D : Fin N → ℂ := RCLike.ofReal ∘ hY.eigenvalues with hDdef
  have hD : ∀ j, D j = (hY.eigenvalues j : ℂ) := fun j => rfl
  have hUU : U * Uᴴ = 1 := by
    simpa [U, star_eq_conjTranspose] using Unitary.coe_mul_star_self hY.eigenvectorUnitary
  have hUU' : Uᴴ * U = 1 := by
    simpa [U, star_eq_conjTranspose] using Unitary.coe_star_mul_self hY.eigenvectorUnitary
  have hspec : Y = U * diagonal D * Uᴴ := by
    conv_lhs => rw [hY.spectral_theorem]
    simp [U, D, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  set c : Fin i → Fin N := Fin.castLE hi with hc
  set A : Matrix (Fin i) (Fin N) ℂ := U.submatrix c id with hA
  have hsub : ∀ d : Fin N → ℂ, (U * diagonal d * Uᴴ).submatrix c c = A * diagonal d * Aᴴ := by
    intro d; ext a b; simp [A, Matrix.mul_apply, conjTranspose_apply]
  have hAA : A * Aᴴ = 1 := by
    have := hsub (fun _ => 1)
    rw [diagonal_one, Matrix.mul_one, Matrix.mul_one, hUU] at this
    rw [← this]; ext a b; simp [one_apply, c]
  set W : Finset (Fin N) → ℂ := fun J =>
    ((Aᴴ * A).submatrix (fun x : J => (x : Fin N)) (fun x : J => (x : Fin N))).det with hWdef
  have hWnn : ∀ J, 0 ≤ W J := by
    intro J
    have e : (Aᴴ * A).submatrix (fun x : J => (x : Fin N)) (fun x : J => (x : Fin N))
        = (A.submatrix id (fun x : J => (x : Fin N)))ᴴ * A.submatrix id (fun x : J => (x : Fin N)) := by
      rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
        Matrix.conjTranspose_submatrix A id (fun x : J => (x : Fin N))]
    have hp := posSemidef_conjTranspose_mul_self (A.submatrix id (fun x : J => (x : Fin N)))
    rw [← e] at hp
    exact hp.det_nonneg
  set w : Finset (Fin N) → ℝ := fun J => (W J).re with hwdef
  have hw0 : ∀ J, 0 ≤ w J := fun J => (Complex.nonneg_iff.mp (hWnn J)).1
  have hW : ∀ J, W J = (w J : ℂ) := fun J => by
    have := (Complex.nonneg_iff.mp (hWnn J)).2
    apply Complex.ext <;> simp [w, this.symm]
  have key : ∀ d : Fin N → ℂ, (A * diagonal d * Aᴴ).det
      = ∑ J ∈ powersetCard i (univ : Finset (Fin N)), (∏ j ∈ J, d j) * (w J : ℂ) := by
    intro d; rw [det_mul_diagonal_mul_eq_sum]
    refine sum_congr rfl fun J _ => ?_
    rw [← hW J]
  have mom : ∀ (ν : Fin N → ℂ) (m : ℕ),
      ∑ J ∈ powersetCard i (univ : Finset (Fin N)), (∏ j ∈ J, (1 + X * C (ν j))).coeff m * (w J : ℂ)
      = (det (1 + (X : ℂ[X]) • (A * diagonal ν * Aᴴ).map C)).coeff m := by
    intro ν m
    rw [← moment A hAA ν m]
    refine sum_congr rfl fun J _ => ?_
    rw [← hW J]
  have hdiag : ∀ a, ((Y a a).re : ℂ) = Y a a := fun a => by simpa using hY.coe_re_apply_self a

  have m1 : ∑ J ∈ powersetCard i (univ : Finset (Fin N)), (w J : ℂ) * (∑ j ∈ J, D j)
      = ∑ a : Fin i, Y (c a) (c a) := by
    have h := mom D 1
    rw [coeff_det_one_add_X_smul_one, ← hsub, ← hspec] at h
    rw [show ∑ a : Fin i, Y (c a) (c a) = trace (Y.submatrix c c) from rfl, ← h]
    refine sum_congr rfl fun J _ => ?_
    rw [(coeff_prod_one_add D J).2.1, mul_comm]
  refine ⟨w, hw0, ?_, ?_, ?_, ?_⟩
  · have h := key (fun _ => 1)
    rw [diagonal_one, Matrix.mul_one, hAA, det_one] at h
    simp only [prod_const_one, one_mul] at h
    exact_mod_cast h.symm
  · have hexp : NormedSpace.exp Y = U * diagonal (fun j => Complex.exp (D j)) * Uᴴ := by
      let u : (Matrix (Fin N) (Fin N) ℂ)ˣ := ⟨U, Uᴴ, hUU, hUU'⟩
      have h := Matrix.exp_units_conj u (diagonal D)
      rw [hspec]
      change NormedSpace.exp ((u : Matrix (Fin N) (Fin N) ℂ) * diagonal D * ((u⁻¹ : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Matrix (Fin N) (Fin N) ℂ)) = _
      rw [h, Matrix.exp_diagonal, Pi.exp_def]
      simp only [← Complex.exp_eq_exp_ℂ]
      rfl
    unfold Formalism.NuclearRankWeightBounds.D.lead
    rw [dif_pos hi, hexp]
    change ((U * _ * Uᴴ).submatrix c c).det = _
    rw [hsub, key]
    push_cast
    refine sum_congr rfl fun J _ => ?_
    rw [mul_comm, ← Complex.exp_sum]
    simp only [hD]
  · apply Complex.ofReal_injective
    push_cast
    simp_rw [hdiag]
    rw [← sum_castLE_eq hi, ← m1]
    simp only [hD]
  · set F := univ.filter (fun a : Fin N => a.val < i) with hF
    set G := univ.filter (fun b : Fin N => i ≤ b.val) with hGdef
    have h2 := mom D 2
    rw [← hsub, ← hspec] at h2
    have h3 := two_coeff_two_det (Y.submatrix c c) (hY.submatrix c)
    have hYY : Y * Y = U * diagonal (fun j => D j * D j) * Uᴴ := by
      rw [hspec]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hUU', Matrix.one_mul, ← Matrix.mul_assoc (diagonal D) (diagonal D),
        diagonal_mul_diagonal]
    have hq := mom (fun j => D j * D j) 1
    rw [coeff_det_one_add_X_smul_one, ← hsub, ← hYY] at hq
    have hsplit : ∀ J : Finset (Fin N), (∑ j ∈ J, D j) ^ 2
        = (∏ j ∈ J, (1 + X * C (D j * D j))).coeff 1 + 2 * (∏ j ∈ J, (1 + X * C (D j))).coeff 2 := by
      intro J
      rw [(coeff_prod_one_add _ J).2.1, (coeff_prod_one_add D J).2.2]
      simp [pow_two]
    have hcx : ∑ J ∈ powersetCard i (univ : Finset (Fin N)), (w J : ℂ) * (∑ j ∈ J, D j) ^ 2
        = trace ((Y * Y).submatrix c c) + ((trace (Y.submatrix c c)) ^ 2
            - trace (Y.submatrix c c * Y.submatrix c c)) := by
      rw [← h3, ← hq, ← h2, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun J _ => ?_
      rw [hsplit]; ring
    have t1 : trace ((Y * Y).submatrix c c) = ∑ a : Fin i, ∑ b : Fin N, Y (c a) b * Y b (c a) := by
      simp [trace, mul_apply]
    have t2 : trace (Y.submatrix c c * Y.submatrix c c)
        = ∑ a : Fin i, ∑ a' : Fin i, Y (c a) (c a') * Y (c a') (c a) := by
      simp [trace, mul_apply]
    have t0 : trace (Y.submatrix c c) = ∑ a : Fin i, Y (c a) (c a) := rfl
    have hG : ∀ f : Fin N → ℂ, ∑ b, f b = ∑ b ∈ F, f b + ∑ b ∈ G, f b := by
      intro f
      rw [← sum_filter_add_sum_filter_not univ (fun b : Fin N => b.val < i)]
      simp only [not_lt, F, G]
    have hrow : ∀ a : Fin i, ∑ b : Fin N, Y (c a) b * Y b (c a)
        = ∑ a' : Fin i, Y (c a) (c a') * Y (c a') (c a) + ∑ b ∈ G, Y (c a) b * Y b (c a) := by
      intro a
      rw [hG, sum_castLE_eq hi (fun b => Y (c a) b * Y b (c a))]
    have hn : ∀ x b : Fin N, ((‖Y x b‖ : ℂ)) ^ 2 = Y x b * Y b x := by
      intro x b
      rw [← hY.apply b x, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    apply Complex.ofReal_injective
    push_cast
    simp_rw [hdiag]
    rw [← sum_castLE_eq hi (fun a => Y a a),
      ← sum_castLE_eq hi (fun a => ∑ b ∈ G, (‖Y a b‖ : ℂ) ^ 2)]
    simp_rw [hn]
    simp only [← hD]
    rw [hcx, t0, t1, t2]
    simp_rw [hrow]
    rw [sum_add_distrib]
    ring

end Formalism.NuclearRankWeightBounds.P
