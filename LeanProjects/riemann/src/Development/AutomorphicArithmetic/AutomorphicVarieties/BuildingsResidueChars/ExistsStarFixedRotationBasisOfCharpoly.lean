import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIsUnitDetMulMapStarEqOfUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFixedRotationBasisOfCharpoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

private theorem star_fixed_eq {K : Type} [Field K] [CharZero K] (Δ : K) (z : Lsq K Δ) (h : star z = z) :
    algebraMap K (Lsq K Δ) z.re = z := by
  have him : -z.im = z.im := by simpa using congrArg QuadraticAlgebra.im h
  have h0 : z.im = 0 := by
    have h2 : (2 : K) * z.im = 0 := by linear_combination -him
    simpa using h2
  ext
  · simp
  · simp [h0]

private theorem star_algebraMap {K : Type} [Field K] (Δ : K) (x : K) :
    star (algebraMap K (Lsq K Δ) x) = algebraMap K (Lsq K Δ) x := by
  ext <;> simp

private theorem map_star_mulVec {R : Type} [CommRing R] [StarRing R] (A : Matrix (Fin 3) (Fin 3) R) (y : Fin 3 → R) :
    star (A *ᵥ y) = A.map star *ᵥ star y := by
  funext i
  exact RingHom.map_mulVec (starRingEnd R) A y i

private theorem conj_fixed {R : Type} [CommRing R] [StarRing R] (B N Q : Matrix (Fin 3) (Fin 3) R)
    (hB : B * B.map star = 1) (hNB : N * B = B * N.map star) (hQu : IsUnit Q.det) (hQ : B * Q.map star = Q) :
    (Q⁻¹ * N * Q).map star = Q⁻¹ * N * Q := by
  have hRQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQu
  have hmul : ∀ X Y : Matrix (Fin 3) (Fin 3) R, (X * Y).map star = X.map star * Y.map star :=
    fun X Y => Matrix.map_mul (f := starRingEnd R)
  have hone : (1 : Matrix (Fin 3) (Fin 3) R).map star = 1 :=
    Matrix.map_one (starRingEnd R) (map_zero _) (map_one _)
  have hBs : B.map star * B = 1 := mul_eq_one_comm.1 hB
  have hRsQs : (Q⁻¹).map star * Q.map star = 1 := by rw [← hmul, hRQ, hone]
  have hQsRs : Q.map star * (Q⁻¹).map star = 1 := mul_eq_one_comm.1 hRsQs
  have hRB : Q⁻¹ * B = (Q⁻¹).map star := by
    calc Q⁻¹ * B = Q⁻¹ * B * (Q.map star * (Q⁻¹).map star) := by rw [hQsRs, mul_one]
      _ = Q⁻¹ * (B * Q.map star) * (Q⁻¹).map star := by simp only [Matrix.mul_assoc]
      _ = (Q⁻¹).map star := by rw [hQ, hRQ, one_mul]
  have hNs : N.map star = B.map star * N * B := by
    rw [Matrix.mul_assoc, hNB, ← Matrix.mul_assoc, hBs, one_mul]
  rw [hmul, hmul, hNs]
  calc (Q⁻¹).map star * (B.map star * N * B) * Q.map star
      = (Q⁻¹).map star * B.map star * N * (B * Q.map star) := by simp only [Matrix.mul_assoc]
    _ = (Q⁻¹ * B) * B.map star * N * Q := by rw [hQ, hRB]
    _ = Q⁻¹ * (B * B.map star) * N * Q := by simp only [Matrix.mul_assoc]
    _ = Q⁻¹ * N * Q := by rw [hB, Matrix.mul_one]

private theorem det_unit {K R : Type} [Field K] [CommRing R] (A : K →+* R) (Q : Matrix (Fin 3) (Fin 3) R)
    (hQu : IsUnit Q.det) (a b c : Fin 3 → K) (hdet : (Matrix.of ![a, b, c]).det ≠ 0) :
    IsUnit (Matrix.of ![Q *ᵥ (A ∘ a), Q *ᵥ (A ∘ b), Q *ᵥ (A ∘ c)]).det := by
  have hfac : Matrix.of ![Q *ᵥ (A ∘ a), Q *ᵥ (A ∘ b), Q *ᵥ (A ∘ c)] =
      (Matrix.of ![a, b, c]).map A * Qᵀ := by
    ext i j
    fin_cases i <;> simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [hfac, Matrix.det_mul, Matrix.det_transpose]
  refine IsUnit.mul ?_ hQu
  have : ((Matrix.of ![a, b, c]).map A).det = A (Matrix.of ![a, b, c]).det :=
    (RingHom.map_det A _).symm
  rw [this]
  exact (isUnit_iff_ne_zero.2 hdet).map A

private theorem charpoly_conj' {n R : Type} [Fintype n] [DecidableEq n] [CommRing R] (Q N : Matrix n n R)
    (hRQ : Q⁻¹ * Q = 1) (hQR : Q * Q⁻¹ = 1) : (Q⁻¹ * N * Q).charpoly = N.charpoly := by
  have := Matrix.charpoly_units_conj' (⟨Q, Q⁻¹, hQR, hRQ⟩ : (Matrix n n R)ˣ) N
  simpa using this

private theorem core {K R : Type} [Field K] [CommRing R] [StarRing R] (A : K →+* R)
    (hAinj : Function.Injective A) (hfix : ∀ z : R, star z = z → ∃ x, A x = z)
    (hst : ∀ x, star (A x) = A x) (τ : K)
    (hI : ∀ M : Matrix (Fin 3) (Fin 3) K,
      M.charpoly = (Polynomial.X - 1) * (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X + 1) →
      ∃ e v : Fin 3 → K, M *ᵥ e = e ∧ M *ᵥ (M *ᵥ v) = τ • (M *ᵥ v) - v ∧ (Matrix.of ![e, v, M *ᵥ v]).det ≠ 0)
    (B N Q : Matrix (Fin 3) (Fin 3) R) (hB : B * B.map star = 1) (hNB : N * B = B * N.map star)
    (hchar : N.charpoly = (Polynomial.X - 1) * (Polynomial.X ^ 2 - Polynomial.C (A τ) * Polynomial.X + 1))
    (hQu : IsUnit Q.det) (hQ : B * Q.map star = Q) :
    ∃ e v : Fin 3 → R, B *ᵥ star e = e ∧ B *ᵥ star v = v ∧ N *ᵥ e = e ∧
      N *ᵥ (N *ᵥ v) = A τ • (N *ᵥ v) - v ∧ IsUnit (Matrix.of ![e, v, N *ᵥ v]).det := by
  have hRQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQu
  have hQR : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ hQu
  have hfx := conj_fixed B N Q hB hNB hQu hQ
  have hex : ∀ i j, ∃ x, A x = (Q⁻¹ * N * Q) i j := fun i j =>
    hfix _ (congrFun (congrFun hfx i) j)
  choose m hm using hex
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 3) (Fin 3) K, M.map A = Q⁻¹ * N * Q := by
    refine ⟨Matrix.of m, ?_⟩
    ext i j
    exact hm i j
  have hcp : (Q⁻¹ * N * Q).charpoly = N.charpoly := charpoly_conj' Q N hRQ hQR
  have hMc : M.charpoly = (Polynomial.X - 1) * (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X + 1) := by
    apply Polynomial.map_injective A hAinj
    rw [← Matrix.charpoly_map, hM, hcp, hchar]
    simp
  obtain ⟨e₀, v₀, he, hv, hdet⟩ := hI M hMc
  have hL : ∀ x : Fin 3 → K, (Q⁻¹ * N * Q) *ᵥ (A ∘ x) = A ∘ (M *ᵥ x) := by
    intro x
    funext i
    rw [← hM]
    exact (RingHom.map_mulVec A M x i).symm
  have hN : ∀ x : Fin 3 → K, N *ᵥ (Q *ᵥ (A ∘ x)) = Q *ᵥ (A ∘ (M *ᵥ x)) := by
    intro x
    rw [← hL, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQR, one_mul]
  have hS : ∀ x : Fin 3 → K, B *ᵥ star (Q *ᵥ (A ∘ x)) = Q *ᵥ (A ∘ x) := by
    intro x
    have : star (A ∘ x) = A ∘ x := by
      funext i
      exact hst (x i)
    rw [map_star_mulVec, this, Matrix.mulVec_mulVec, hQ]
  refine ⟨Q *ᵥ (A ∘ e₀), Q *ᵥ (A ∘ v₀), hS _, hS _, ?_, ?_, ?_⟩
  · rw [hN, he]
  · rw [hN, hN, hv]
    have : A ∘ (τ • (M *ᵥ v₀) - v₀) = A τ • (A ∘ (M *ᵥ v₀)) - A ∘ v₀ := by
      funext i
      simp
    rw [this, Matrix.mulVec_sub, Matrix.mulVec_smul]
  · rw [hN]
    exact det_unit A Q hQu _ _ _ hdet

theorem UpperTheory.exists_star_fixed_rotation_basis_of_charpoly :
    ∀ (K : Type) [Field K] [CharZero K] (Δ τ : K), Δ ≠ 0 → τ ^ 2 - 4 ≠ 0 → ∀ B N : Matrix (Fin 3) (Fin 3) (Lsq K Δ),
        B * B.map star = 1 → N * B = B * N.map star →
        N.charpoly = (Polynomial.X - 1) * (Polynomial.X ^ 2 - Polynomial.C (algebraMap K (Lsq K Δ) τ) * Polynomial.X + 1) →
        ∃ e v : Fin 3 → Lsq K Δ, B *ᵥ star e = e ∧ B *ᵥ star v = v ∧ N *ᵥ e = e ∧
          N *ᵥ (N *ᵥ v) = algebraMap K (Lsq K Δ) τ • (N *ᵥ v) - v ∧ IsUnit (Matrix.of ![e, v, N *ᵥ v]).det := by
  intro K _ _ Δ τ hΔ hτ B N hB hNB hchar
  obtain ⟨Q, hQu, hQ⟩ := UpperTheory.exists_isUnit_det_mul_map_star_eq_of_unitary K Δ hΔ B hB
  refine core (algebraMap K (Lsq K Δ)) ?_ (fun z hz => ⟨z.re, star_fixed_eq Δ z hz⟩) (star_algebraMap Δ) τ
    (UpperTheory.exists_fixed_rotation_basis_of_charpoly K τ hτ) B N Q hB hNB hchar hQu hQ
  intro x y h
  simpa using congrArg QuadraticAlgebra.re h
