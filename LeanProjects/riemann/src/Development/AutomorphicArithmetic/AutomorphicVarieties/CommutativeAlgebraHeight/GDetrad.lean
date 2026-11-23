import Mathlib

open IsLocalRing

private theorem exists_col {K : Type} [Field K] {n : ℕ} (a : Fin (n+1) → K) (ha : a ≠ 0) :
    ∃ U : Matrix (Fin (n+1)) (Fin (n+1)) K, U.det ≠ 0 ∧ ∀ i, U i 0 = a i := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  refine ⟨((1 : Matrix (Fin (n+1)) (Fin (n+1)) K).updateCol i a).submatrix id (Equiv.swap 0 i), ?_, ?_⟩
  · rw [Matrix.det_permute', ← Matrix.cramer_apply, Matrix.cramer_one]
    refine mul_ne_zero ?_ (by simpa using hi)
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (0 : Fin (n+1)) i)) with h | h <;> simp [h]
  · intro j
    simp

private def Emat (K : Type) [CommRing K] (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) K :=
  Matrix.diagonal (fun i => if i = 0 then 0 else 1)

private theorem exists_param {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (m : Fin (n+1) → K) (h1 : M.mulVec m = 0) (h2 : M.det = 0) :
    ∃ (N U : Matrix (Fin (n+1)) (Fin (n+1)) K) (t : K),
      N * Emat K n * U.adjugate = M ∧ ∀ i, t * U i 0 = m i := by
  have : ∃ (a : Fin (n+1) → K) (t : K), a ≠ 0 ∧ M.mulVec a = 0 ∧ ∀ i, t * a i = m i := by
    by_cases hm : m = 0
    · obtain ⟨a, ha, hMa⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h2
      exact ⟨a, 0, ha, hMa, by simp [hm]⟩
    · exact ⟨m, 1, hm, h1, by simp⟩
  obtain ⟨a, t, ha, hMa, hta⟩ := this
  obtain ⟨U, hU, hUa⟩ := exists_col a ha
  refine ⟨(U.det)⁻¹ • (M * U), U, t, ?_, fun i => by rw [hUa, hta]⟩
  have hE : M * U * Emat K n = M * U := by
    ext i j
    rw [Emat, Matrix.mul_diagonal]
    by_cases hj : j = 0
    · subst hj
      have := congrFun hMa i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      simp [Matrix.mul_apply, hUa, this]
    · simp [hj]
  rw [Matrix.smul_mul, hE, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul,
    Matrix.mul_one, smul_smul, inv_mul_cancel₀ hU, one_smul]

private theorem param_mulVec {B : Type} [CommRing B] {n : ℕ} (N U : Matrix (Fin (n+1)) (Fin (n+1)) B)
    (t : B) (a : Fin (n+1)) :
    ∑ b, (N * Emat B n * U.adjugate) a b * (t * U b 0) = 0 := by
  have h : (N * Emat B n * U.adjugate * U) a 0 = 0 := by
    rw [Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply,
      Emat, Matrix.mul_diagonal]
    simp
  rw [Matrix.mul_apply] at h
  calc _ = t * ∑ b, (N * Emat B n * U.adjugate) a b * U b 0 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by ring)
    _ = 0 := by rw [h, mul_zero]

private theorem param_det {B : Type} [CommRing B] {n : ℕ} (N U : Matrix (Fin (n+1)) (Fin (n+1)) B) :
    (N * Emat B n * U.adjugate).det = 0 := by
  have : (Emat B n).det = 0 := by
    rw [Emat, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ 0) (by simp)
  simp [Matrix.det_mul, this]

private abbrev Bv (n : ℕ) := Option ((Fin (n+1) × Fin (n+1)) ⊕ (Fin (n+1) × Fin (n+1)))

private noncomputable def phi (R : Type) [CommRing R] (n : ℕ) :
    MvPolynomial ((Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) R →ₐ[R] MvPolynomial (Bv n) R :=
  MvPolynomial.aeval (Sum.elim
    (fun p => (((Matrix.of fun a b => (MvPolynomial.X (some (Sum.inl (a, b))) : MvPolynomial (Bv n) R))
      * Emat (MvPolynomial (Bv n) R) n * (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inr (a, b))) : MvPolynomial (Bv n) R)).adjugate : Matrix (Fin (n+1)) (Fin (n+1)) (MvPolynomial (Bv n) R))) p.1 p.2)
    (fun i => MvPolynomial.X none * MvPolynomial.X (some (Sum.inr (i, 0)))))

private theorem factor (R : Type) [CommRing R] (n : ℕ) {K : Type} [Field K] [Algebra R K]
    (ψ : MvPolynomial ((Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) R →ₐ[R] K)
    (h1 : ∀ a, ψ (∑ b : Fin (n + 1), MvPolynomial.X (Sum.inl (a, b)) * MvPolynomial.X (Sum.inr b)) = 0)
    (h2 : ψ (Matrix.det (Matrix.of fun a b : Fin (n + 1) => MvPolynomial.X (Sum.inl (a, b)))) = 0)
    (f) (hf : phi R n f = 0) : ψ f = 0 := by
  obtain ⟨N, U, t, hM, hm⟩ := exists_param (Matrix.of fun a b => ψ (MvPolynomial.X (Sum.inl (a, b))))
    (fun b => ψ (MvPolynomial.X (Sum.inr b)))
    (by ext a; simpa [Matrix.mulVec, dotProduct] using h1 a)
    (by rw [AlgHom.map_det] at h2; exact h2)
  let χ : MvPolynomial (Bv n) R →ₐ[R] K := MvPolynomial.aeval
    (fun o => Option.elim o t (Sum.elim (fun p => N p.1 p.2) (fun p => U p.1 p.2)))
  have hc : χ.comp (phi R n) = ψ := by
    apply MvPolynomial.algHom_ext
    rintro (⟨a, b⟩ | i)
    · have e1 : χ.mapMatrix (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inl (a, b))) : MvPolynomial (Bv n) R)) = N := by
        ext a b; simp [χ]
      have e2 : χ.mapMatrix (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inr (a, b))) : MvPolynomial (Bv n) R)) = U := by
        ext a b; simp [χ]
      have e3 : χ.mapMatrix (Emat _ n) = Emat K n := by
        ext a b; simp [Emat, Matrix.diagonal_apply]; split_ifs <;> simp
      have e4 := congrFun (congrFun hM a) b
      rw [← e1, ← e2, ← e3, ← AlgHom.map_adjugate, ← map_mul, ← map_mul] at e4
      simpa [phi] using e4
    · simpa [phi, χ] using hm i
  rw [← hc, AlgHom.comp_apply, hf, map_zero]

private theorem phi_row (R : Type) [CommRing R] (n : ℕ) (a : Fin (n+1)) :
    phi R n (∑ b : Fin (n + 1), MvPolynomial.X (Sum.inl (a, b)) * MvPolynomial.X (Sum.inr b)) = 0 := by
  rw [map_sum, ← param_mulVec (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inl (a, b))) : MvPolynomial (Bv n) R)) (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inr (a, b))) : MvPolynomial (Bv n) R)) (MvPolynomial.X none) a]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [map_mul, phi, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  rfl

private theorem phi_det (R : Type) [CommRing R] (n : ℕ) :
    phi R n (Matrix.det (Matrix.of fun a b : Fin (n + 1) => MvPolynomial.X (Sum.inl (a, b)))) = 0 := by
  rw [AlgHom.map_det, ← param_det (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inl (a, b))) : MvPolynomial (Bv n) R)) (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inr (a, b))) : MvPolynomial (Bv n) R))]
  congr 1
  ext1 a b
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, phi, MvPolynomial.aeval_X]
  rfl

theorem UpperTheory.V.CA.g_detrad :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ),
      let A := MvPolynomial ((Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) R
      let I : Ideal A := Ideal.span (Set.range (fun a : Fin (n + 1) => ∑ b : Fin (n + 1), (MvPolynomial.X (Sum.inl (a, b)) * MvPolynomial.X (Sum.inr b) : A)) ∪ {Matrix.det (Matrix.of fun a b : Fin (n + 1) => (MvPolynomial.X (Sum.inl (a, b)) : A))})
      I.radical.IsPrime ∧ (MvPolynomial.X (Sum.inr 0) : A) ∉ I.radical ∧ (∀ r : R, MvPolynomial.C r ∈ I.radical → r = 0) ∧
        ∀ f ∈ I.radical, ∀ d : ℕ, MvPolynomial.homogeneousComponent d f ∈ I.radical := by
  intro R _ _ n A I
  have hP : (RingHom.ker (phi R n)).IsPrime := RingHom.ker_isPrime _
  have hle : I ≤ RingHom.ker (phi R n) := by
    rw [Ideal.span_le]
    rintro x (⟨a, rfl⟩ | rfl)
    · exact phi_row R n a
    · exact phi_det R n
  have heq : I.radical = RingHom.ker (phi R n) := by
    apply le_antisymm (hP.radical_le_iff.mpr hle)
    rw [Ideal.radical_eq_sInf]
    apply le_sInf
    rintro q ⟨hIq, hq⟩ f hf
    let ψ : A →ₐ[R] FractionRing (A ⧸ q) :=
      (IsScalarTower.toAlgHom R (A ⧸ q) (FractionRing (A ⧸ q))).comp (Ideal.Quotient.mkₐ R q)
    have hψ : ∀ g, ψ g = 0 ↔ g ∈ q := by
      intro g
      simp [ψ, Ideal.Quotient.eq_zero_iff_mem]
    rw [← hψ]
    refine factor R n ψ (fun a => ?_) ?_ f hf
    · rw [hψ]; exact hIq (Ideal.subset_span (Or.inl ⟨a, rfl⟩))
    · rw [hψ]; exact hIq (Ideal.subset_span (Or.inr rfl))
  refine ⟨heq ▸ hP, ?_, ?_, ?_⟩
  · rw [heq, RingHom.mem_ker]
    simp [phi, MvPolynomial.X_ne_zero]
  · intro r hr
    rw [heq, RingHom.mem_ker] at hr
    simpa [phi] using hr
  · letI := MvPolynomial.gradedAlgebra (σ := (Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) (R := R)
    have hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ R) := by
      apply Ideal.homogeneous_span
      rintro x (⟨a, rfl⟩ | rfl)
      · refine ⟨1 + 1, ?_⟩
        rw [MvPolynomial.mem_homogeneousSubmodule]
        exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun b _ =>
          (MvPolynomial.isHomogeneous_X _ _).mul (MvPolynomial.isHomogeneous_X _ _))
      · refine ⟨∑ _i : Fin (n+1), 1, ?_⟩
        rw [Matrix.det_apply]
        refine Submodule.sum_mem _ (fun σ _ => ?_)
        rw [Units.smul_def]
        refine zsmul_mem ?_ _
        rw [MvPolynomial.mem_homogeneousSubmodule]
        exact MvPolynomial.IsHomogeneous.prod _ _ (fun _ => 1) (fun b _ => MvPolynomial.isHomogeneous_X _ _)
    intro f hf d
    have := hI.radical d hf
    rw [← MvPolynomial.decomposition.decompose'_apply]
    exact this
