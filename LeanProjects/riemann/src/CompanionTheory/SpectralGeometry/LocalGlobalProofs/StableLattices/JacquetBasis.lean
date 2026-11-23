import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp

noncomputable section

open Matrix CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.GradEig

variable {n : ℕ}

theorem Jm_mul_self (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem trace_eq_zero {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ} (h : IsGrad ε A) : A.trace = 0 := by
  obtain ⟨hG, hH, -, -⟩ := h
  have hG' : A.conjTranspose * Jm ε + Jm ε * A = 0 := hG
  rw [hH] at hG'
  have h1 : A * Jm ε = -(Jm ε * A) := eq_neg_of_add_eq_zero_left hG'
  have h2 : (A * Jm ε * Jm ε).trace = -(Jm ε * A * Jm ε).trace := by
    rw [h1, Matrix.neg_mul, Matrix.trace_neg]
  rw [Matrix.mul_assoc A, Jm_mul_self, Matrix.mul_one, Matrix.trace_mul_cycle, Jm_mul_self,
    Matrix.one_mul] at h2
  linear_combination h2 / 2

theorem eigenvalue_cases {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (h3 : A * A * A = A) (i : Fin n) :
    hA.eigenvalues i = -1 ∨ hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 1 := by
  have hev := hA.mulVec_eigenvectorBasis i
  obtain ⟨v, hv⟩ : ∃ v, v = (hA.eigenvectorBasis i).ofLp := ⟨_, rfl⟩
  rw [← hv] at hev
  obtain ⟨r, hr⟩ : ∃ r, r = hA.eigenvalues i := ⟨_, rfl⟩
  rw [← hr] at hev ⊢
  have h3v : (A * A * A) *ᵥ v = (r ^ 3) • v := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    simp only [hev, Matrix.mulVec_smul, smul_smul]
    congr 1
    ring
  rw [h3, hev] at h3v
  have hne : v ≠ 0 := by
    intro h0
    have h1 : ‖hA.eigenvectorBasis i‖ = 1 := (hA.eigenvectorBasis).orthonormal.1 i
    have h2 : hA.eigenvectorBasis i = 0 := by
      rw [hv] at h0
      simpa using h0
    rw [h2, norm_zero] at h1
    exact zero_ne_one h1
  have hr3 : r ^ 3 = r := by
    have h4 : (r ^ 3 - r) • v = 0 := by rw [sub_smul, ← h3v, sub_self]
    rcases smul_eq_zero.1 h4 with h5 | h5
    · exact sub_eq_zero.1 h5
    · exact absurd h5 hne
  have hf : r * (r - 1) * (r + 1) = 0 := by linear_combination hr3
  rcases mul_eq_zero.1 hf with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by linarith))
  · exact Or.inl (by linarith)

theorem exists_perm_blocks {c : Fin n → Fin 3} {d : Fin 3 → ℕ} (hd : ∑ i, d i = n)
    (hc : ∀ i, Fintype.card {x // c x = i} = d i) :
    ∃ σ : Fin n ≃ Fin n, ∀ p, c (σ p) = ((stdBlocks d hd).symm p).1 := by
  classical
  let e : ∀ i, {x // c x = i} ≃ Fin (d i) := fun i => Fintype.equivFinOfCardEq (hc i)
  let τ : Fin n ≃ Fin n :=
    ((Equiv.sigmaFiberEquiv c).symm.trans (Equiv.sigmaCongrRight e)).trans (stdBlocks d hd)
  refine ⟨τ.symm, fun p => ?_⟩
  have hτ : τ.symm p = (((e ((stdBlocks d hd).symm p).1).symm ((stdBlocks d hd).symm p).2) : Fin n) := rfl
  rw [hτ]
  exact ((e _).symm _).2

theorem exists_gradBasis {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ} (h : IsGrad ε A) :
    Nonempty (GradBasis A) := by
  classical
  have htr := trace_eq_zero h
  obtain ⟨_, hH, h3, _⟩ := h
  have hA : A.IsHermitian := hH
  have hcase := eigenvalue_cases hA h3
  let c : Fin n → Fin 3 := fun x =>
    if hA.eigenvalues x = -1 then 0 else if hA.eigenvalues x = 0 then 1 else 2
  have hc0 : ∀ x, c x = 0 ↔ hA.eigenvalues x = -1 := by
    intro x; rcases hcase x with hx | hx | hx <;> norm_num [c, hx] <;> decide
  have hc1 : ∀ x, c x = 1 ↔ hA.eigenvalues x = 0 := by
    intro x; rcases hcase x with hx | hx | hx <;> norm_num [c, hx] <;> decide
  have hc2 : ∀ x, c x = 2 ↔ hA.eigenvalues x = 1 := by
    intro x; rcases hcase x with hx | hx | hx <;> norm_num [c, hx] <;> decide
  have hval : ∀ x, (![-1, 0, 1] : Fin 3 → ℂ) (c x) = ((hA.eigenvalues x : ℝ) : ℂ) := by
    intro x; rcases hcase x with hx | hx | hx <;> norm_num [c, hx] <;> rfl
  obtain ⟨j, hj⟩ : ∃ j, (Finset.univ.filter fun x => hA.eigenvalues x = -1).card = j := ⟨_, rfl⟩
  have hsumR : ∑ x, hA.eigenvalues x = 0 := by
    have h1 := hA.trace_eq_sum_eigenvalues
    rw [htr] at h1
    have h2 := congrArg Complex.re h1
    simpa [Complex.re_sum] using h2.symm
  have hk1 : (Finset.univ.filter fun x => hA.eigenvalues x = 1).card = j := by
    have hs : ∑ x, hA.eigenvalues x = ∑ x, ((if hA.eigenvalues x = 1 then (1 : ℝ) else 0) -
        (if hA.eigenvalues x = -1 then (1 : ℝ) else 0)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rcases hcase x with hx | hx | hx <;> norm_num [hx]
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, hsumR, hj] at hs
    have hs' : ((Finset.univ.filter fun x => hA.eigenvalues x = 1).card : ℝ) = j := by linarith
    exact_mod_cast hs'
  have htot : j + (Finset.univ.filter fun x => hA.eigenvalues x = 0).card + j = n := by
    have hs : ∑ x : Fin n, ((if hA.eigenvalues x = -1 then 1 else 0) +
        (if hA.eigenvalues x = 0 then 1 else 0) + (if hA.eigenvalues x = 1 then 1 else 0) : ℕ) =
        ∑ x : Fin n, 1 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rcases hcase x with hx | hx | hx <;> norm_num [hx]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole,
      Finset.sum_boole, hj, hk1] at hs
    simpa using hs
  have hcard : ∀ i, Fintype.card {x // c x = i} = dims n j i := by
    intro i
    fin_cases i
    · show Fintype.card {x // c x = 0} = j
      rw [Fintype.card_subtype, Finset.filter_congr fun x _ => hc0 x, hj]
    · show Fintype.card {x // c x = 1} = n - 2 * j
      rw [Fintype.card_subtype, Finset.filter_congr fun x _ => hc1 x]
      omega
    · show Fintype.card {x // c x = 2} = j
      rw [Fintype.card_subtype, Finset.filter_congr fun x _ => hc2 x, hk1]
  have hd : ∑ i, dims n j i = n := by
    rw [Fin.sum_univ_three]
    show j + (n - 2 * j) + j = n
    omega
  obtain ⟨σ, hσ⟩ := exists_perm_blocks hd hcard
  have hs := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have hUU : (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 hA.eigenvectorUnitary.2
  have hUU' : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 hA.eigenvectorUnitary.2
  have hdiag : (diagonal fun p => (![-1, 0, 1] : Fin 3 → ℂ) ((stdBlocks (dims n j) hd).symm p).fst) =
      (diagonal (RCLike.ofReal ∘ hA.eigenvalues)).submatrix σ σ := by
    rw [Matrix.submatrix_diagonal_equiv]
    congr 1
    funext p
    rw [← hσ p, hval]
    rfl
  have e1 : (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix id σ *
      (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)).submatrix σ id = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ σ.bijective, hUU, Matrix.submatrix_id_id]
  have e2 : (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)).submatrix σ id *
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix id σ = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hUU', Matrix.submatrix_one_equiv]
  have e3 : A = ((hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix id σ *
      diagonal fun p => (![-1, 0, 1] : Fin 3 → ℂ) ((stdBlocks (dims n j) hd).symm p).fst) *
      (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)).submatrix σ id := by
    rw [hdiag, ← Matrix.submatrix_mul _ _ _ _ _ σ.bijective,
      ← Matrix.submatrix_mul _ _ _ _ _ σ.bijective, Matrix.submatrix_id_id]
    exact hs
  exact ⟨⟨_, _, e1, e2, j, hd, e3⟩⟩

end GlobalTheory.CompanionTheory.GradEig

theorem GlobalTheory.CompanionTheory.GradEig.basis : CompanionTheory.RgExh.Dec.J.Basis := by
  intro n ε A h
  exact GlobalTheory.CompanionTheory.GradEig.exists_gradBasis h
