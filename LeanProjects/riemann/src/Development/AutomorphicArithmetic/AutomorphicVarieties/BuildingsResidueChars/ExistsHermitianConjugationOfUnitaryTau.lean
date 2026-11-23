import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

section Abs

variable {L A : Type} [CommRing L] [Ring A] [Algebra L A]

private def Psi (t : L) (n e : A) (z : Etau L t) : A := z.re • e + z.im • (n * e)

private theorem Psi_mul {t : L} {n e : A} (hee : e * e = e) (hc : n * e = e * n)
    (hn : n * (n * e) = t • (n * e) - e) (z z' : Etau L t) :
    Psi t n e (z * z') = Psi t n e z * Psi t n e z' := by
  have h1 : e * (n * e) = n * e := by rw [← mul_assoc, ← hc, mul_assoc, hee]
  have h2 : n * e * e = n * e := by rw [mul_assoc, hee]
  have h3 : n * e * (n * e) = t • (n * e) - e := by rw [mul_assoc, h1, hn]
  simp only [Psi, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, add_mul, mul_add,
    smul_mul_smul_comm, hee, h1, h2, h3]
  module

end Abs

section Core

variable {L : Type} [CommRing L] [StarRing L]

private theorem core_lemma {R A : Type} [CommRing R] [Ring A] [Algebra R A] {t c : R} {M E : A}
    (hc : c * (2 - t) = 1) (hCH : (M - 1) * (M * M - t • M + 1) = 0)
    (hE : E = 1 - c • (M * M - t • M + 1)) :
    E * E = E ∧ M * E = E * M ∧ M * (M * E) = t • (M * E) - E ∧ M * (1 - E) = 1 - E := by
  set P := M * M - t • M + 1 with hP
  have hMP : M * P = P := by
    rw [sub_mul, one_mul, sub_eq_zero] at hCH
    exact hCH
  have hMP2 : M * (M * P) = P := by rw [hMP, hMP]
  have hPM : P * M = P := by
    have h : P * M = M * P := by
      simp only [hP, add_mul, sub_mul, mul_add, mul_sub, smul_mul_assoc, mul_smul_comm,
        mul_one, one_mul, mul_assoc]
    rw [h, hMP]
  have hPP : P * P = (2 - t) • P := by
    nth_rewrite 1 [hP]
    simp only [add_mul, sub_mul, smul_mul_assoc, one_mul, mul_assoc, hMP2, hMP]
    module
  have key : (c * (2 - t)) • P = P := by rw [hc, one_smul]
  have hcc : c * c * (2 - t) = c := by rw [mul_assoc, hc, mul_one]
  subst hE
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_smul_comm, hPP, smul_smul, hcc]
    abel
  · simp only [sub_mul, mul_sub, one_mul, mul_one, mul_smul_comm, smul_mul_assoc, hMP, hPM]
  · simp only [mul_sub, mul_one, mul_smul_comm, hMP, smul_sub]
    linear_combination (norm := module) hP - key
  · simp only [sub_sub_cancel, mul_smul_comm, hMP]

private theorem H_affine_combination_eq_of_quadratic_relation {R A : Type} [CommRing R] [Ring A] [Algebra R A] {t : R} {M E : A}
    (hee : E * E = E) (hc : M * E = E * M) (hn : M * (M * E) = t • (M * E) - E)
    (z z' : Etau R t) :
    ((1 - E) + Psi t M E z) * ((1 - E) + Psi t M E z') = (1 - E) + Psi t M E (z * z') := by
  have hEME : E * (M * E) = M * E := by rw [hc, ← mul_assoc, hee]
  have hMEE : M * E * E = M * E := by rw [mul_assoc, hee]
  have h0 : (1 - E) * Psi t M E z' = 0 := by
    simp only [Psi, mul_add, mul_smul_comm, sub_mul, one_mul, hee, hEME, sub_self, smul_zero,
      add_zero]
  have h1 : Psi t M E z * (1 - E) = 0 := by
    simp only [Psi, add_mul, smul_mul_assoc, mul_sub, mul_one, hee, hMEE, sub_self, smul_zero,
      add_zero]
  have h2 : (1 - E) * (1 - E) = 1 - E := by
    simp only [mul_sub, sub_mul, one_mul, mul_one, hee, sub_self, sub_zero]
  rw [add_mul, mul_add, mul_add, Psi_mul hee hc hn, h0, h1, h2, add_zero, zero_add]

private theorem sgn_eigen_perp_span_spec {R A : Type} [CommRing R] [Ring A] [Algebra R A] {t : R} {M E : A}
    (hn : M * (M * E) = t • (M * E) - E) (hM1 : M * (1 - E) = 1 - E) (z : Etau R t) :
    M * ((1 - E) + Psi t M E z) = (1 - E) + Psi t M E (QuadraticAlgebra.omega * z) := by
  simp only [Psi, mul_add, mul_smul_comm, hM1, hn, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul, QuadraticAlgebra.omega]
  module

private theorem one_sub_add_psi_one_eq_one {R A : Type} [CommRing R] [Ring A] [Algebra R A] {t : R} {M E : A} :
    (1 - E) + Psi t M E (1 : Etau R t) = 1 := by
  simp [Psi, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem mul_one_sub_add_psi_eq_of_conj {R A : Type} [CommRing R] [Ring A] [Algebra R A] {t c : R}
    {X M₁ M₂ E₁ E₂ : A} (h : X * M₁ = M₂ * X)
    (hE₁ : E₁ = 1 - c • (M₁ * M₁ - t • M₁ + 1)) (hE₂ : E₂ = 1 - c • (M₂ * M₂ - t • M₂ + 1))
    (z : Etau R t) :
    X * ((1 - E₁) + Psi t M₁ E₁ z) = ((1 - E₂) + Psi t M₂ E₂ z) * X := by
  have h2 : X * (M₁ * M₁) = M₂ * M₂ * X := by rw [← mul_assoc, h, mul_assoc, h, mul_assoc]
  have hXP : X * (M₁ * M₁ - t • M₁ + 1) = (M₂ * M₂ - t • M₂ + 1) * X := by
    simp only [mul_add, mul_sub, add_mul, sub_mul, mul_smul_comm, smul_mul_assoc, h2, h,
      one_mul, mul_one]
  have hXE : X * E₁ = E₂ * X := by
    subst hE₁ hE₂
    simp only [mul_sub, sub_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, hXP]
  have hXME : X * (M₁ * E₁) = M₂ * E₂ * X := by
    rw [← mul_assoc, h, mul_assoc, hXE, mul_assoc]
  simp only [Psi, mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, mul_smul_comm,
    smul_mul_assoc, hXE, hXME]

private theorem lintegral_mul_wt_eq_lintegral_mul_wt_conj (X Y : Matrix (Fin 3) (Fin 3) L) :
    (X * Y).map star = X.map star * Y.map star := by
  ext i j
  simp [Matrix.mul_apply, star_sum, star_mul']

private theorem sub_map_star_fin_three (X Y : Matrix (Fin 3) (Fin 3) L) :
    (X - Y).map star = X.map star - Y.map star := by
  ext i j
  simp

private theorem add_map_star_fin_three (X Y : Matrix (Fin 3) (Fin 3) L) :
    (X + Y).map star = X.map star + Y.map star := by
  ext i j
  simp

private theorem smul_map_star_fin_three (a : L) (X : Matrix (Fin 3) (Fin 3) L) :
    (a • X).map star = star a • X.map star := by
  ext i j
  simp [star_mul']

private theorem one_map_star_fin_three : (1 : Matrix (Fin 3) (Fin 3) L).map star = 1 := by
  ext i j
  rw [Matrix.map_apply]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

private theorem zero_map_star_fin_three : (0 : Matrix (Fin 3) (Fin 3) L).map star = 0 := by
  ext i j
  simp

private theorem map_star_map_star_fin_three (X : Matrix (Fin 3) (Fin 3) L) : (X.map star).map star = X := by
  ext i j
  simp

private theorem core (t c : L) (ht : star t = t) (hc' : star c = c) (hc : c * (2 - t) = 1)
    (d u : Etau L t) (hdu : d * u = 1)
    (hu : u * (⟨star u.re, star u.im⟩ : Etau L t) * QuadraticAlgebra.omega = 1)
    (D N : Matrix (Fin 3) (Fin 3) L) (hN : N = D * D.map star)
    (hCH : (N - 1) * (N * N - t • N + 1) = 0) :
    ∃ B : Matrix (Fin 3) (Fin 3) L, B * B.map star = 1 ∧ N * B = B * N.map star ∧
      ∀ w : Fin 3 → L, B *ᵥ star w = w →
        (N *ᵥ w = w → D *ᵥ star w = w) ∧
        (N *ᵥ (N *ᵥ w) = t • (N *ᵥ w) - w → D *ᵥ star w = d.re • w + d.im • (N *ᵥ w)) := by
  obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin 3) (Fin 3) L, E = 1 - c • (N * N - t • N + 1) := ⟨_, rfl⟩
  obtain ⟨Eb, hEb⟩ : ∃ E : Matrix (Fin 3) (Fin 3) L,
      E = 1 - c • (N.map star * N.map star - t • N.map star + 1) := ⟨_, rfl⟩
  have hNb : N.map star = D.map star * D := by rw [hN, lintegral_mul_wt_eq_lintegral_mul_wt_conj, map_star_map_star_fin_three]
  have hN' : D * D.map star = N := hN.symm
  have hCHb : (N.map star - 1) * (N.map star * N.map star - t • N.map star + 1) = 0 := by
    have h := congrArg (fun X => X.map star) hCH
    simp only [lintegral_mul_wt_eq_lintegral_mul_wt_conj, sub_map_star_fin_three, add_map_star_fin_three, smul_map_star_fin_three, one_map_star_fin_three, zero_map_star_fin_three, ht] at h
    exact h
  obtain ⟨hee, hc1, hn, hM1⟩ := core_lemma hc hCH hE
  obtain ⟨heeb, hcb, hnb, hM1b⟩ := core_lemma hc hCHb hEb
  have hEstar : Eb.map star = E := by
    rw [hEb, hE]
    simp only [lintegral_mul_wt_eq_lintegral_mul_wt_conj, sub_map_star_fin_three, add_map_star_fin_three, smul_map_star_fin_three, one_map_star_fin_three, map_star_map_star_fin_three, hc', ht]
  have hFstar : ((1 - Eb) + Psi t (N.map star) Eb u).map star =
      (1 - E) + Psi t N E ⟨star u.re, star u.im⟩ := by
    simp only [Psi, lintegral_mul_wt_eq_lintegral_mul_wt_conj, sub_map_star_fin_three, add_map_star_fin_three, smul_map_star_fin_three, one_map_star_fin_three, map_star_map_star_fin_three, hEstar]
  have hDNb : D * N.map star = N * D := by rw [hNb, ← mul_assoc, hN']
  have hDbN : D.map star * N = N.map star * D.map star := by rw [hNb, mul_assoc, hN']
  have hu' : QuadraticAlgebra.omega * (u * (⟨star u.re, star u.im⟩ : Etau L t)) = 1 := by
    rw [← hu]
    ring
  refine ⟨D * ((1 - Eb) + Psi t (N.map star) Eb u), ?_, ?_, ?_⟩
  · have h5 := mul_one_sub_add_psi_eq_of_conj hDbN hE hEb u
    rw [lintegral_mul_wt_eq_lintegral_mul_wt_conj, hFstar]
    calc _ = D * (((1 - Eb) + Psi t (N.map star) Eb u) * D.map star) *
          ((1 - E) + Psi t N E ⟨star u.re, star u.im⟩) := by simp only [mul_assoc]
      _ = D * (D.map star * ((1 - E) + Psi t N E u)) *
          ((1 - E) + Psi t N E ⟨star u.re, star u.im⟩) := by rw [h5]
      _ = N * (((1 - E) + Psi t N E u) * ((1 - E) + Psi t N E ⟨star u.re, star u.im⟩)) := by
          rw [← mul_assoc D, hN', mul_assoc]
      _ = 1 := by rw [H_affine_combination_eq_of_quadratic_relation hee hc1 hn, sgn_eigen_perp_span_spec hn hM1, hu', one_sub_add_psi_one_eq_one]
  · have h5b := mul_one_sub_add_psi_eq_of_conj (X := N.map star) rfl hEb hEb u
    calc N * (D * ((1 - Eb) + Psi t (N.map star) Eb u))
        = D * N.map star * ((1 - Eb) + Psi t (N.map star) Eb u) := by rw [← mul_assoc, hDNb]
      _ = D * (((1 - Eb) + Psi t (N.map star) Eb u) * N.map star) := by rw [mul_assoc, h5b]
      _ = _ := by rw [mul_assoc]
  · intro w hw
    have h5d := mul_one_sub_add_psi_eq_of_conj hDNb hEb hE u
    have key : D *ᵥ star w = ((1 - E) + Psi t N E d) *ᵥ w := by
      conv_rhs => rw [← hw]
      rw [Matrix.mulVec_mulVec, h5d, ← mul_assoc, H_affine_combination_eq_of_quadratic_relation hee hc1 hn, hdu, one_sub_add_psi_one_eq_one, one_mul]
    refine ⟨fun hNw => ?_, fun hNw => ?_⟩
    · have hEw : E *ᵥ w = 0 := by
        rw [hE]
        simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
          Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hNw]
        rw [show w - t • w + w = (2 - t) • w by module, smul_smul, hc, one_smul, sub_self]
      rw [key]
      simp only [Psi, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
        Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hEw, Matrix.mulVec_zero, smul_zero,
        sub_zero, add_zero]
    · have hEw : E *ᵥ w = w := by
        rw [hE]
        simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
          Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hNw]
        module
      rw [key]
      simp only [Psi, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
        Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hEw]
      abel

end Core

theorem UpperTheory.exists_hermitian_conjugation_of_unitary_tau :
    ∀ (K : Type) [Field K] [CharZero K] (Δ τ : K), τ ^ 2 - 4 ≠ 0 → ∀ d : EL Δ τ, d * sigL d = ofE Δ (QuadraticAlgebra.omega : Etau K τ) →
        ∀ δ : U3 Δ, HasTau δ τ → ∀ N : Matrix (Fin 3) (Fin 3) (Lsq K Δ), N = ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) →
        ∃ B : Matrix (Fin 3) (Fin 3) (Lsq K Δ), B * B.map star = 1 ∧ N * B = B * N.map star ∧
          ∀ w : Fin 3 → Lsq K Δ, B *ᵥ star w = w →
            (N *ᵥ w = w → (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star w = w) ∧
            (N *ᵥ (N *ᵥ w) = algebraMap K (Lsq K Δ) τ • (N *ᵥ w) - w →
              (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star w = d.re • w + d.im • (N *ᵥ w)) := by
  intro K _ _ Δ τ hτ d hd δ hδ N hN
  have hstar : ∀ x : K, star (algebraMap K (Lsq K Δ) x) = algebraMap K (Lsq K Δ) x := by
    intro x
    ext <;> simp [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]
  have h2 : (2 : K) - τ ≠ 0 := by
    intro h
    apply hτ
    have : τ = 2 := by linear_combination -h
    rw [this]
    norm_num
  have hc : algebraMap K (Lsq K Δ) (2 - τ)⁻¹ * (2 - algebraMap K (Lsq K Δ) τ) = 1 := by
    rw [← map_ofNat (algebraMap K (Lsq K Δ)) 2, ← map_sub, ← map_mul, inv_mul_cancel₀ h2,
      map_one]
  obtain ⟨v, hv⟩ : ∃ v : EL Δ τ, v = ⟨algebraMap K (Lsq K Δ) τ, -1⟩ := ⟨_, rfl⟩
  have hωv : (QuadraticAlgebra.omega : EL Δ τ) * v = 1 := by
    rw [hv]
    ext <;> simp [QuadraticAlgebra.omega, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> ring
  have hofE : ofE Δ (QuadraticAlgebra.omega : Etau K τ) = QuadraticAlgebra.omega := by
    ext <;> simp [ofE, QuadraticAlgebra.omega]
  obtain ⟨u, hu⟩ : ∃ u : EL Δ τ, u = sigL d * v := ⟨_, rfl⟩
  have hdu : d * u = 1 := by rw [hu, ← mul_assoc, hd, hofE, hωv]
  have hus : (⟨star u.re, star u.im⟩ : EL Δ τ) = d * v := by
    rw [hu, hv]
    ext <;> simp [sigL, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, star_mul', hstar] <;> ring
  have huu : u * (⟨star u.re, star u.im⟩ : EL Δ τ) * QuadraticAlgebra.omega = 1 := by
    rw [hus]
    calc u * (d * v) * QuadraticAlgebra.omega
        = (d * sigL d) * (QuadraticAlgebra.omega * v) * v := by rw [hu]; ring
      _ = 1 := by rw [hd, hofE, hωv, mul_one, hωv]
  have hN' : N = (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *
      (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map star := by
    rw [hN]
    rfl
  have hCH : (N - 1) * (N * N - algebraMap K (Lsq K Δ) τ • N + 1) = 0 := by
    have h := Matrix.aeval_self_charpoly N
    have hcp : N.charpoly = (Polynomial.X - 1) * (Polynomial.X ^ 2 -
        Polynomial.C (algebraMap K (Lsq K Δ) τ) * Polynomial.X + 1) := by
      rw [hN]
      exact hδ
    rw [hcp] at h
    simp only [map_mul, map_sub, map_add, map_one, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C] at h
    rw [Algebra.smul_def, ← sq]
    exact h
  exact core (algebraMap K (Lsq K Δ) τ) (algebraMap K (Lsq K Δ) (2 - τ)⁻¹) (hstar τ) (hstar _) hc
    d u hdu huu (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) N hN' hCH
