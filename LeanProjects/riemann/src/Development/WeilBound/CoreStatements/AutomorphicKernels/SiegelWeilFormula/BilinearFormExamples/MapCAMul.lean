import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SDarb
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.BfEqSumRight

set_option linter.unusedSectionVars false

noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {m n : ℕ}

theorem hTens_eq {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (c : AE F E →ₐ[AF F] AE F E)
    (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (x y : Matrix α β (AE F E)) :
    hTens c JA JB x y = (x * (JB * (y.map c)ᵀ * JAᵀ)).trace := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

theorem map_cA_mul {σ : E →ₐ[F] E} {a b c : Type} [Fintype b] (x : Matrix a b (AE F E)) (y : Matrix b c (AE F E)) :
    (x * y).map (cA σ) = x.map (cA σ) * y.map (cA σ) := by
  ext i j; simp [Matrix.mul_apply, map_sum, map_mul]

theorem incM_jeps (ε : ℤˣ) : incM F (jeps (E := E) n ε) =
    Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 := by
  ext (i | i) (j | j) <;> simp [jeps, incM, Matrix.one_apply] <;> split_ifs <;> simp

theorem incM_dbl (YJ : Matrix (Fin n) (Fin n) E) : dbl (incM F YJ) = incM F (dbl YJ) := by
  ext (i | i) (j | j) <;> simp [dbl, incM]

theorem incM_b (b : GL (Fin n ⊕ Fin n) E) :
    (incM F b.1)ᵀ = Matrix.fromRows (incM F b.1.toCols₁)ᵀ (incM F b.1.toCols₂)ᵀ := by
  ext (i | i) j <;> rfl

theorem tr_swap (JA : Matrix (Fin m) (Fin m) (AE F E)) (Z W : Mx F E m n) :
    (Z * Wᵀ * JAᵀ).trace = (Zᵀ * JA * W).trace := by
  rw [← Matrix.trace_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]

theorem symp_frame (σ : E →ₐ[F] E) (JA : Matrix (Fin m) (Fin m) E) (YJ : Matrix (Fin n) (Fin n) E)
    (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ) (hb : b.1ᵀ * dbl YJ * b.1.map σ = jeps n ε) (Z X Z' X' : Mx F E m n) :
    symp (R := AF F) (cA σ) (-1) (incM F JA) (dbl (incM F YJ)) (Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ)
      (Z' * (incM F b.1.toCols₁)ᵀ + X' * (incM F b.1.toCols₂)ᵀ) = -(Bf σ JA Z X' + ((ε : ℤ) : AF F) * Bf σ JA X Z') := by
  have hw : ∀ Z X : Mx F E m n, Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ =
      Matrix.fromCols Z X * (incM F b.1)ᵀ := fun Z X => by
    rw [incM_b, Matrix.fromCols_mul_fromRows]
  rw [hw, hw, symp, hTens_eq, map_cA_mul]
  have hN : (incM F b.1)ᵀ * dbl (incM F YJ) * ((incM F b.1)ᵀ.map (cA σ))ᵀ = incM F (jeps n ε) := by
    rw [← hb, incM_dbl, Matrix.transpose_map, map_cA_incM, Matrix.transpose_transpose, incM_mul, incM_mul, incM_transpose]
  rw [Matrix.transpose_mul]
  simp only [← Matrix.mul_assoc]
  have hN' : Matrix.fromCols Z X * (incM F b.1)ᵀ * dbl (incM F YJ) * ((incM F b.1)ᵀ.map (cA σ))ᵀ =
      (Matrix.fromCols Z X * (incM F (jeps (E := E) n ε) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :
        Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) := by
    rw [← hN]; simp only [Matrix.mul_assoc]
  have hc : (Matrix.fromCols Z' X').map (cA σ) = Matrix.fromCols (Z'.map (cA σ)) (X'.map (cA σ)) := by
    ext i (j | j) <;> rfl
  rw [hN', hc, Matrix.transpose_fromCols, incM_jeps, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mul,
    Matrix.trace_add, Matrix.trace_smul, tr_swap]
  have key : ∀ t : AE F E, Algebra.trace (AF F) (AE F E) (((ε : ℤ) : AE F E) * t) =
      ((ε : ℤ) : AF F) * Algebra.trace (AF F) (AE F E) t := fun t => by
    rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
  have key2 : ∀ t : AE F E, Algebra.trace (AF F) (AE F E) (((ε : ℤ) : AE F E) • t) =
      ((ε : ℤ) : AF F) * Algebra.trace (AF F) (AE F E) t := fun t => by rw [smul_eq_mul, key]
  have key3 : ∀ t : AE F E, Algebra.trace (AF F) (AE F E) (t * ((ε : ℤ) : AE F E)) =
      ((ε : ℤ) : AF F) * Algebra.trace (AF F) (AE F E) t := fun t => by rw [mul_comm, key]
  simp only [Bf, neg_one_mul, map_neg, map_add, key, key2, key3]
  ring

end PositivityTheory.SiegelWeilFormula.Ldexa
