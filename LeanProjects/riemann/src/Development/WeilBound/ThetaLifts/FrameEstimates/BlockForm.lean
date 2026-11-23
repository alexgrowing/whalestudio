import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange

noncomputable section

namespace PositivityTheory.ThKEst

open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace SignatureOfHermitianForm

theorem sig_sq {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : r + s = n) (A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ)
    (hA : Aᵀ * M * A.map star = Matrix.fromBlocks 1 0 0 (-1)) :
    M.det ≠ 0 ∧ Function.Surjective A.mulVec := by
  let e : Fin n ≃ Fin r ⊕ Fin s := (finCongr h.symm).trans finSumFinEquiv.symm
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e
  have h1 : A'ᵀ * M * A'.map star
      = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).submatrix e e := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply]
  have h2 : A'.det * M.det * (A'.map star).det ≠ 0 := by
    rw [← Matrix.det_transpose A', ← Matrix.det_mul, ← Matrix.det_mul, h1, Matrix.det_submatrix_equiv_self,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    simp
  have h3 : A'.det ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul h2)
  refine ⟨right_ne_zero_of_mul (left_ne_zero_of_mul h2), fun x => ?_⟩
  have hu : IsUnit A' := (Matrix.isUnit_iff_isUnit_det A').2 (Ne.isUnit h3)
  obtain ⟨u, hu⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hu x
  refine ⟨u ∘ e.symm, ?_⟩
  rw [← hu]
  ext i
  simp only [A', Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id, Function.comp]
  rw [← e.sum_comp]
  simp

theorem block_form {r s : ℕ} (w : Fin r ⊕ Fin s → ℂ) :
    w ⬝ᵥ (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)) *ᵥ star w
      = ((∑ i, Complex.normSq (w (Sum.inl i)) - ∑ j, Complex.normSq (w (Sum.inr j)) : ℝ) : ℂ) := by
  rw [Matrix.fromBlocks_mulVec]
  simp [dotProduct, Fintype.sum_sum_type, Matrix.neg_mulVec, Complex.mul_conj, sub_eq_add_neg]

theorem sig_index {n r s k : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) (c : ℂ) (hc : c ≠ 0)
    (x y : Fin k → Fin n → ℂ) (hxx : ∀ i j, x i ⬝ᵥ M *ᵥ star (x j) = 0)
    (hxy : ∀ i j, x i ⬝ᵥ M *ᵥ star (y j) = if i = j then c else 0) : k ≤ min r s := by
  obtain ⟨h, A, hA⟩ := h
  choose u hu using fun i => (sig_sq h A hA).2 (x i)
  let L : (Fin k → ℂ) →ₗ[ℂ] (Fin r ⊕ Fin s → ℂ) := Fintype.linearCombination ℂ u
  have hL : ∀ v, A *ᵥ L v = ∑ i, v i • x i := by
    intro v
    simp only [L, Fintype.linearCombination_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, hu]
  have hinj : ∀ v, L v = 0 → v = 0 := by
    intro v hv
    have h0 := hL v
    rw [hv, Matrix.mulVec_zero] at h0
    ext j
    have h1 := congrArg (fun z => z ⬝ᵥ M *ᵥ star (y j)) h0
    simp only [zero_dotProduct, sum_dotProduct, smul_dotProduct, hxy, smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_right hc
  have hiso : ∀ v, ∑ i, Complex.normSq (L v (Sum.inl i)) = ∑ j, Complex.normSq (L v (Sum.inr j)) := by
    intro v
    have h1 := block_form (L v)
    have h2 : (A *ᵥ L v) ⬝ᵥ M *ᵥ star (A *ᵥ L v) = 0 := by
      rw [hL]
      simp only [star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, smul_dotProduct,
        dotProduct_sum, dotProduct_smul, hxx, smul_zero, Finset.sum_const_zero]
    have h3 : star (A *ᵥ L v) = A.map star *ᵥ star (L v) := by
      ext i
      simp [Matrix.mulVec, dotProduct]
    rw [h3, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hA, h1] at h2
    exact sub_eq_zero.1 (Complex.ofReal_eq_zero.1 h2)
  have hz : ∀ {m : ℕ} (f : Fin m → ℂ), ∑ i, Complex.normSq (f i) = 0 → ∀ i, f i = 0 := by
    intro m f hf i
    exact Complex.normSq_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg (f i)).1 hf i (Finset.mem_univ i))
  refine le_min ?_ ?_
  · have := LinearMap.finrank_le_finrank_of_injective (f := (LinearMap.funLeft ℂ ℂ Sum.inl) ∘ₗ L) (by
      rw [injective_iff_map_eq_zero]
      intro v hv
      have h1 : ∀ i, L v (Sum.inl i) = 0 := fun i => congrFun hv i
      have h2 := hz (fun j => L v (Sum.inr j)) (by rw [← hiso]; simp [h1])
      apply hinj
      ext (i | j)
      · exact h1 i
      · exact h2 j)
    simpa using this
  · have := LinearMap.finrank_le_finrank_of_injective (f := (LinearMap.funLeft ℂ ℂ Sum.inr) ∘ₗ L) (by
      rw [injective_iff_map_eq_zero]
      intro v hv
      have h1 : ∀ i, L v (Sum.inr i) = 0 := fun i => congrFun hv i
      have h2 := hz (fun j => L v (Sum.inl j)) (by rw [hiso]; simp [h1])
      apply hinj
      ext (i | j)
      · exact h2 i
      · exact h1 j)
    simpa using this

theorem form_map {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (τ : E →+* ℂ)
    (hτ : ∀ x, τ (σ x) = star (τ x)) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : ℂ) (x y : Fin n → E) :
    (fun i => τ (x i)) ⬝ᵥ (c • J.map τ) *ᵥ star (fun i => τ (y i)) = c * τ (x ⬝ᵥ J *ᵥ fun i => σ (y i)) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  simp [dotProduct, Matrix.mulVec, hτ]

theorem of_sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (τ : E →+* ℂ) (hτ : ∀ x, τ (σ x) = star (τ x)) {n r s : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : ℂ) (hc : c ≠ 0)
    (h : HasSig (c • J.map τ) r s) :
    J.det ≠ 0 ∧ r + s = n ∧ ∀ fr : Frame σ J, fr.IsGood → fr.r ≤ min r s := by
  refine ⟨?_, h.1, fun fr hfr => ?_⟩
  · obtain ⟨h, A, hA⟩ := h
    intro h0
    apply (sig_sq h A hA).1
    have : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
    rw [Matrix.det_smul, this, h0, map_zero, mul_zero]
  · refine sig_index h c hc (fun i l => τ (fr.x i l)) (fun i l => τ (fr.y i l)) (fun i j => ?_) (fun i j => ?_)
    · have := hfr.xx i j
      unfold form at this
      rw [form_map σ τ hτ, this, map_zero, mul_zero]
    · have := hfr.xy i j
      unfold form at this
      rw [form_map σ τ hτ, this]
      split_ifs <;> simp

end SignatureOfHermitianForm

theorem epsOf_of : EpsOf := by
  intro F E _ _ _ _ _ σ B hB n X r s hX
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hτ := hB.cm.2.2.2 (B.emb w).1
  rcases hX with hX | hX
  · have := SignatureOfHermitianForm.of_sig σ _ hτ X.J 1 one_ne_zero (r := r) (s := s) (by rw [one_smul]; exact hX.sig w)
    exact ⟨⟨Or.inl hX.herm, this.1⟩, this.2⟩
  · have := SignatureOfHermitianForm.of_sig σ _ hτ X.J Complex.I Complex.I_ne_zero (hX.sig w)
    exact ⟨⟨Or.inr hX.skew, this.1⟩, this.2⟩

end PositivityTheory.ThKEst
