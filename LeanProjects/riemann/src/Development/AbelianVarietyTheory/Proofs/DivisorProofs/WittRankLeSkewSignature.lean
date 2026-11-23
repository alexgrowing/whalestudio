import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.WittBound

open Matrix

theorem quad_mulVec {n k : Type} [Fintype n] [Fintype k] (M : Matrix n n ℂ) (P : Matrix n k ℂ) (x : k → ℂ) :
    (P *ᵥ x) ⬝ᵥ (M *ᵥ star (P *ᵥ x)) = x ⬝ᵥ ((P.transpose * M * P.map star) *ᵥ star x) := by
  have hs : star (P *ᵥ x) = P.map star *ᵥ star x := by
    funext i; simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
  rw [hs, ← Matrix.vecMul_transpose P x, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem quad_neg {n : Type} [Fintype n] (M : Matrix n n ℂ) (u : n → ℂ) :
    (-u) ⬝ᵥ (M *ᵥ star (-u)) = u ⬝ᵥ (M *ᵥ star u) := by
  simp [star_neg, Matrix.mulVec_neg]

theorem sum_mul_star_eq_zero {p : Type} [Fintype p] (y : p → ℂ) (h : ∑ i, y i * star (y i) = 0) : y = 0 := by
  have h' : ∑ i, Complex.normSq (y i) = 0 := by
    have : ((∑ i, Complex.normSq (y i) : ℝ) : ℂ) = 0 := by
      rw [Complex.ofReal_sum]; simpa [Complex.mul_conj] using h
    exact_mod_cast this
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (y j))).1 h' i (Finset.mem_univ _)
  simpa using this

end GlobalTheory.WittBound

namespace GlobalTheory.WittBound

open Matrix

theorem add_le {n r m : ℕ} {ι : Type} [Fintype ι] (M : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin r) ℂ)
    (hV : V.transpose * M * V.map star = 0) (hinj : ∀ x, V *ᵥ x = 0 → x = 0)
    (A : Matrix (Fin n) ι ℂ) (e : (Fin m → ℂ) →ₗ[ℂ] (ι → ℂ))
    (he : ∀ y, e y ⬝ᵥ ((A.transpose * M * A.map star) *ᵥ star (e y)) = 0 → y = 0) : r + m ≤ n := by
  let f : ((Fin r → ℂ) × (Fin m → ℂ)) →ₗ[ℂ] (Fin n → ℂ) := LinearMap.coprod V.mulVecLin (A.mulVecLin ∘ₗ e)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, y⟩ hxy
    have h1 : V *ᵥ x + A *ᵥ e y = 0 := by simpa [f] using hxy
    have h2 : A *ᵥ e y = -(V *ᵥ x) := eq_neg_of_add_eq_zero_right h1
    have hy : y = 0 := by
      apply he
      rw [← quad_mulVec, h2, quad_neg, quad_mulVec, hV]
      simp
    subst hy
    have hx : x = 0 := hinj x (by simpa using h1)
    simp [hx]
  have := LinearMap.finrank_le_finrank_of_injective hf
  simpa [Module.finrank_prod, Module.finrank_fin_fun] using this

end GlobalTheory.WittBound

namespace GlobalTheory.WittBound

open Matrix

def inlVec (p q : ℕ) : (Fin p → ℂ) →ₗ[ℂ] (Fin p ⊕ Fin q → ℂ) where
  toFun y := Sum.elim y 0
  map_add' y y' := by funext i; cases i <;> simp
  map_smul' c y := by funext i; cases i <;> simp

def inrVec (p q : ℕ) : (Fin q → ℂ) →ₗ[ℂ] (Fin p ⊕ Fin q → ℂ) where
  toFun y := Sum.elim 0 y
  map_add' y y' := by funext i; cases i <;> simp
  map_smul' c y := by funext i; cases i <;> simp

theorem sig_bound {n r p q : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : HasSig M p q) (V : Matrix (Fin n) (Fin r) ℂ)
    (hV : V.transpose * M * V.map star = 0) (hinj : ∀ x, V *ᵥ x = 0 → x = 0) : r ≤ p ∧ r ≤ q := by
  obtain ⟨hn, A, hA⟩ := hM
  constructor
  · have := add_le M V hV hinj A (inrVec p q) (fun y hy => by
      rw [hA] at hy
      apply sum_mul_star_eq_zero
      have : -(∑ i, y i * star (y i)) = 0 := by
        simpa [inrVec, Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Function.comp_def, Pi.star_apply,
          Matrix.neg_mulVec, Matrix.one_mulVec, Finset.sum_neg_distrib] using hy
      simpa using this)
    omega
  · have := add_le M V hV hinj A (inlVec p q) (fun y hy => by
      rw [hA] at hy
      apply sum_mul_star_eq_zero
      simpa [inlVec, Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type] using hy)
    omega

end GlobalTheory.WittBound

namespace GlobalTheory.WittBound

open Matrix

theorem wittIndex_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n : ℕ) (W : Spc F E n) (r' s' : ℕ), B.IsGood σ → W.IsSkew σ B r' s' →
    ∀ (c : E), c ≠ 0 → σ c = -c → ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ (c • W.J.map σ) Xf Yf →
      r ≤ r' ∧ r ≤ s' := by
  intro F E _ _ _ _ _ σ B n W r' s' hB hW c hc _ r Xf Yf hfr
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  set τ : E →+* ℂ := (B.emb w).1 with hτdef
  have hτσ : ∀ x, τ (σ x) = star (τ x) := fun x => hB.cm.2.2.2 τ x
  set τ' : E →+* ℂ := (starRingEnd ℂ).comp τ with hτ'def
  have hτ'σ : ∀ x, τ' (σ x) = τ x := by intro x; simp [τ', hτσ]
  set V : Matrix (Fin n) (Fin r) ℂ := Xf.map τ with hVdef
  have hT : (Formalism.UG.cT (σ : E →+* E) Xf).map τ' = V.transpose := by
    ext i j; simp [Formalism.UG.cT, V, hτ'σ]
  have hJ : (c • W.J.map σ).map τ' = τ' c • W.J.map τ := by
    ext i j; simp [hτ'σ]
  have hX : Xf.map τ' = V.map star := by
    ext i j; simp [V, τ']
  have h0 : V.transpose * (τ' c • W.J.map τ) * V.map star = 0 := by
    have := congrArg (fun M => M.map τ') hfr.xx
    rw [Matrix.map_mul, Matrix.map_mul, hT, hJ, hX, Matrix.map_zero _ (map_zero τ')] at this
    exact this
  have hc' : τ' c ≠ 0 := by
    intro h; exact hc (τ'.injective (by simpa using h))
  have hK : V.transpose * W.J.map τ * V.map star = 0 := by
    rw [Matrix.mul_smul, Matrix.smul_mul] at h0
    exact (smul_eq_zero.1 h0).resolve_left hc'
  have hV : V.transpose * (Complex.I • W.J.map τ) * V.map star = 0 := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hK, smul_zero]
  have h1 : V.transpose * ((c • W.J.map σ).map τ' * Yf.map τ') = 1 := by
    have := congrArg (fun M => M.map τ') hfr.xy
    rw [Matrix.map_mul, Matrix.map_mul, hT, Matrix.map_one _ (map_zero τ') (map_one τ'), Matrix.mul_assoc] at this
    exact this
  have hinj : ∀ x, V *ᵥ x = 0 → x = 0 := by
    intro x hx
    have h2 := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h2
    calc x = (1 : Matrix (Fin r) (Fin r) ℂ) *ᵥ x := (Matrix.one_mulVec x).symm
      _ = _ := by rw [← h2, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  have hsig := hW.sig w
  have := sig_bound _ hsig V hV hinj
  exact ⟨this.1, this.2⟩

end GlobalTheory.WittBound
