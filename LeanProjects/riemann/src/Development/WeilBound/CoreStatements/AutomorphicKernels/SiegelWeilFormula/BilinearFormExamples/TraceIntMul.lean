import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SDarb
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.MapCAMul

set_option linter.unusedSectionVars false

noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {m n : ℕ}

theorem trace_int_mul (u : ℤ) (t : AE F E) :
    Algebra.trace (AF F) (AE F E) ((u : AE F E) * t) = (u : AF F) * Algebra.trace (AF F) (AE F E) t := by
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]

theorem trace_map_cA {σ : E →ₐ[F] E} {ι : Type} [Fintype ι] (M : Matrix ι ι (AE F E)) :
    (M.map (cA σ)).trace = cA σ M.trace := by
  simp [Matrix.trace, map_sum]

theorem Bf_symm {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) (J : Matrix (Fin m) (Fin m) E) (u : ℤ)
    (hJ : ∀ i j, σ (J j i) = (u : E) * J i j) (X Z : Mx F E m n) :
    Bf σ J X Z = (u : AF F) * Bf σ J Z X := by
  have hJc : (incM F J).map (cA σ) = ((u : ℤ) : AE F E) • (incM F J)ᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
    change cA σ (inclR (F := F) (AF F) (J i j)) = _ * inclR (F := F) (AF F) (J j i)
    rw [show cA σ (inclR (F := F) (AF F) (J i j)) = inclR (F := F) (AF F) (σ (J i j)) from rfl, hJ j i, map_mul, map_intCast]
  have hcc : (Z.map (cA σ)).map (cA σ) = Z := by ext i j; exact cA_cA hσ _
  unfold Bf
  rw [← trace_cA hσ, ← trace_map_cA, map_cA_mul, map_cA_mul, Matrix.transpose_map, hJc, hcc,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, trace_int_mul]
  congr 2
  rw [← Matrix.trace_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem mapS_mul {σ : E →ₐ[F] E} {a b c : Type} [Fintype b] (x : Matrix a b E) (y : Matrix b c E) :
    (x * y).map σ = x.map σ * y.map σ := by
  ext i j; simp [Matrix.mul_apply, map_sum, map_mul]

theorem congr_symm {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) {ι : Type} [Fintype ι] (D b : Matrix ι ι E) (u : ℤ)
    (hD : Dᵀ.map σ = (u : E) • D) : ((bᵀ * D * b.map σ).map σ)ᵀ = (u : E) • (bᵀ * D * b.map σ) := by
  have hbb : (b.map σ).map σ = b := by ext i j; simp [hσ]
  rw [mapS_mul, mapS_mul, hbb, Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.transpose_map,
    ← Matrix.transpose_map, Matrix.transpose_transpose, hD, Matrix.smul_mul, Matrix.mul_smul]
  simp only [Matrix.mul_assoc]

theorem eps_eq {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) (YJ : Matrix (Fin n) (Fin n) E) (u : ℤ)
    (hY : ∀ i j, σ (YJ j i) = (u : E) * YJ i j) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ)
    (hb : b.1ᵀ * dbl YJ * b.1.map σ = jeps n ε) (hn : 1 ≤ n) : (ε : ℤ) = u := by
  have hD : (dbl YJ)ᵀ.map σ = (u : E) • dbl YJ := by
    ext (i | i) (j | j) <;> simp [dbl, hY]
  have h := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E => M (Sum.inl ⟨0, hn⟩) (Sum.inr ⟨0, hn⟩))
    (congr_symm hσ (dbl YJ) b.1 u hD)
  simp only [hb] at h
  simp [jeps] at h
  exact_mod_cast h

end PositivityTheory.SiegelWeilFormula.Ldexa
