import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.PsiNegTrPairGen

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_gramR (σ : E →ₐ[F] E) (θ : Ainf F ⊗[F] E →+* ℂ)
    (hc : ∀ z, θ (sigR (Ainf F) σ z) = star (θ z)) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin n → Fin M → Ainf F ⊗[F] E) :
    (gramR (Ainf F) σ J Y).map θ =
      (Matrix.of fun a j => θ (Y j a))ᴴ * (JR (Ainf F) J).map θ * Matrix.of fun a j => θ (Y j a) := by
  ext a b
  simp only [Matrix.map_apply, gramR, hR, hform, map_sum, map_mul, hc, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem of_eq_crd {M n : ℕ} (θ : Ainf F ⊗[F] E →+* ℂ) (fr : GL (Fin M) ℂ) (g : GL (Fin n) ℂ)
    (Y : Fin n → Fin M → Ainf F ⊗[F] E) :
    (Matrix.of fun a j => θ (Y j a)) = fr.1 * crd θ fr g Y * (g⁻¹).1 := by
  simp only [crd, ← Matrix.mul_assoc]
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem map_gramR_crd (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (ε : ι → Fin M → Bool) (fr : ι → GL (Fin M) ℂ) (hfr : IsFrames J θ ε fr) (g : ι → GL (Fin n) ℂ)
    (Y : Fin n → Fin M → Ainf F ⊗[F] E) (i : ι) :
    (gramR (Ainf F) σ J Y).map (θ i) = (((g i)⁻¹).1)ᴴ * gramX (ε i) (crdAll θ fr g Y i) * ((g i)⁻¹).1 := by
  rw [map_gramR σ (θ i) (hP.conj i), of_eq_crd (θ i) (fr i) (g i)]
  have hg : gramX (ε i) (crdAll θ fr g Y i) =
      (crd (θ i) (fr i) (g i) Y)ᴴ * Matrix.diagonal (sgn (ε i)) * crd (θ i) (fr i) (g i) Y := gramX_eq _ _
  rw [hg, ← hfr i]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem trace_herm_mul {n : ℕ} (β y : WR.E n) :
    (herm β * herm y).trace = ∑ a, ∑ b, ((β a b : ℝ) : ℂ) * ((y a b : ℝ) : ℂ) := by
  have key : ∀ i j, herm β i j * herm y j i + herm β j i * herm y i j =
      ((β i j : ℝ) : ℂ) * ((y i j : ℝ) : ℂ) + ((β j i : ℝ) : ℂ) * ((y j i : ℝ) : ℂ) := by
    intro i j
    apply Complex.ext <;> simp [herm] <;> ring
  have h2 : (2 : ℂ) * (herm β * herm y).trace = 2 * ∑ a, ∑ b, ((β a b : ℝ) : ℂ) * ((y a b : ℝ) : ℂ) := by
    have e1 : (herm β * herm y).trace = ∑ i, ∑ j, herm β i j * herm y j i := by
      simp [Matrix.trace, Matrix.mul_apply]
    have e2 : (2 : ℂ) * ∑ i, ∑ j, herm β i j * herm y j i =
        ∑ i, ∑ j, (herm β i j * herm y j i + herm β j i * herm y i j) := by
      rw [two_mul]
      conv_lhs => arg 2; rw [Finset.sum_comm]
      simp only [Finset.sum_add_distrib]
    have e3 : (2 : ℂ) * ∑ a, ∑ b, ((β a b : ℝ) : ℂ) * ((y a b : ℝ) : ℂ) =
        ∑ i, ∑ j, (((β i j : ℝ) : ℂ) * ((y i j : ℝ) : ℂ) + ((β j i : ℝ) : ℂ) * ((y j i : ℝ) : ℂ)) := by
      rw [two_mul]
      conv_lhs => arg 2; rw [Finset.sum_comm]
      simp only [Finset.sum_add_distrib]
    rw [e1, e2, e3]
    simp only [key]
  exact mul_left_cancel₀ two_ne_zero h2

theorem trace_re_of_herm {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((((A * B).trace).re : ℝ) : ℂ) = (A * B).trace := by
  apply Complex.conj_eq_iff_re.mp
  change star (Matrix.trace _) = _
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq, Matrix.trace_mul_comm]

theorem herm_ybAll (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ} (g : ι → GL (Fin n) ℂ)
    (b : HermR (Ainf F) σ n) (i : ι) :
    herm (ybAll σ θ g b i) =
      ((g i)⁻¹).1 * (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (((g i)⁻¹).1)ᴴ :=
  herm_hinv _ (Matrix.isHermitian_mul_mul_conjTranspose _ (map_isHerm σ (θ i) (hP.conj i) b))

theorem herm_ygAll (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ} (g : ι → GL (Fin n) ℂ)
    (b : HermR (Ainf F) σ n) (i : ι) :
    herm (ygAll σ θ g b i) =
      ((g i).1)ᴴ * (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (g i).1 :=
  herm_hinv _ (Matrix.isHermitian_conjTranspose_mul_mul _ (map_isHerm σ (θ i) (hP.conj i) b))

end PositivityTheory.SiegelWeilFormula.GReal
