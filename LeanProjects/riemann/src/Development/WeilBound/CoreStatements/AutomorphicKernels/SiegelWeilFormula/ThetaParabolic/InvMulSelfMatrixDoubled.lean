import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
import Development.WeilBound.ThetaLifts.LatticeBasics.SiegelWeilAnisoOf
import Development.WeilBound.ThetaLifts.LatticeBasics.SecLaw

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

set_option linter.unusedSectionVars false

namespace PositivityTheory.SiegelWeilFormula.Tpar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_mul {p q r : Type} [Fintype q] (M : Matrix p q E) (N : Matrix q r E) :
    incM F (M * N) = incM F M * incM F N := Matrix.map_mul

theorem incM_add {p q : Type} (M N : Matrix p q E) : incM F (M + N) = incM F M + incM F N :=
  Matrix.map_add _ (map_add _) M N

theorem incM_transpose {p q : Type} (M : Matrix p q E) : incM F Mᵀ = (incM F M)ᵀ := rfl

theorem incM_one {p : Type} [DecidableEq p] : incM F (1 : Matrix p p E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem incM_diagCols (n : ℕ) : incM F (diagCols (Fin n) : Matrix _ _ E) = diagCols (Fin n) := by
  simp only [incM, diagCols, Matrix.fromRows_map, Matrix.map_one _ (map_zero _) (map_one _)]

theorem incM_fromCols {p q r : Type} (M : Matrix p (q ⊕ r) E) :
    incM F M = Matrix.fromCols (incM F M.toCols₁) (incM F M.toCols₂) := by
  conv_lhs => rw [← Matrix.fromCols_toCols M]
  exact Matrix.fromCols_map _ _ _

theorem incM_map_cA {p q : Type} (M : Matrix p q E) : (incM F M).map (cA σ) = incM F (M.map σ) := by
  ext i j
  simp [incM, cA, inclR]

theorem dbl_incM {q : Type} [Fintype q] [DecidableEq q] (J : Matrix q q E) : dbl (incM F J) = incM F (dbl J) := by
  simp only [dbl, incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _)]
  congr 1
  ext i j
  simp

variable {n : ℕ} {Y : Spc F E n}

theorem frame_xy {b : GL (Fin n ⊕ Fin n) E} (h : IsFrame2 σ Y b) :
    b.1.toCols₁ᵀ * dbl Y.J * b.1.toCols₂.map σ = 1 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := h
  rw [← Matrix.fromCols_toCols b.1, Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromCols_map,
    Matrix.fromRows_mul_fromCols] at hε
  exact (Matrix.fromBlocks_inj.1 hε).2.1

theorem frame_xy_A {b : GL (Fin n ⊕ Fin n) E} (h : IsFrame2 σ Y b) :
    (incM F b.1.toCols₁)ᵀ * dbl (incM F Y.J) * (incM F b.1.toCols₂).map (cA σ) = 1 := by
  rw [incM_map_cA, dbl_incM, ← incM_transpose, ← incM_mul, ← incM_mul, frame_xy h, incM_one]

theorem inv_mul_self_matrix_doubled (x : G2 σ Y) : mat2 x⁻¹ * mat2 x = 1 :=
  Units.inv_mul x.1

theorem inFrame_mul {b : GL (Fin n ⊕ Fin n) E} {x : G2 σ Y} {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)}
    (hx : inFrame b x = N) : mat2 x * incM F b.1 = incM F b.1 * N := by
  rw [← hx, inFrame]
  simp only [← Matrix.mul_assoc, ← incM_mul, Units.mul_inv, incM_one, Matrix.one_mul]

theorem inv_mul_frame {x : G2 σ Y} {Bm N N' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)}
    (hx : mat2 x * Bm = Bm * N) (hN : N * N' = 1) : mat2 x⁻¹ * Bm = Bm * N' :=
  calc mat2 x⁻¹ * Bm = mat2 x⁻¹ * Bm * (N * N') := by rw [hN, Matrix.mul_one]
    _ = mat2 x⁻¹ * (mat2 x * Bm) * N' := by rw [hx]; simp only [Matrix.mul_assoc]
    _ = Bm * N' := by rw [← Matrix.mul_assoc, inv_mul_self_matrix_doubled, Matrix.one_mul]

theorem par_of {p q : Type} [Fintype p] [Fintype q] [DecidableEq q] {X : Matrix p p (AE F E)} {D : Matrix p q (AE F E)}
    {T0 T0i P : Matrix q q (AE F E)} (hT : T0 * T0i = 1) (h : X * (D * T0) = D * T0 * P) :
    X * D = D * (T0 * P * T0i) :=
  calc X * D = X * (D * T0) * T0i := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hT, Matrix.mul_one]
    _ = D * (T0 * P * T0i) := by rw [h]; simp only [Matrix.mul_assoc]

theorem hTens_eq {R E' : Type} [CommRing R] [CommRing E'] [Algebra R E'] (c : E' →ₐ[R] E') {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E') (JB : Matrix β β E') (x y : Matrix α β E') :
    hTens c JA JB x y = Matrix.trace (x * JB * (y.map c)ᵀ * JAᵀ) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

variable {m : ℕ}

theorem symp_N (X : Matrix (Fin m) (Fin n) (AE F E)) (β T0 : Matrix (Fin n) (Fin n) (AE F E))
    (By : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) (JA : Matrix (Fin m) (Fin m) (AE F E))
    (JB : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))
    (hf : ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * T0)ᵀ * JB * By.map (cA σ) = 1) :
    symp (R := AF F) (cA σ) (-1) JA JB (-(X * βᵀ * T0ᵀ) * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) (X * Byᵀ) =
      Algebra.trace (AF F) (AE F E) (Matrix.trace (β * (Xᵀ * JA * X.map (cA σ)))) := by
  rw [symp, hTens_eq]
  congr 1
  have e1 : -(X * βᵀ * T0ᵀ) * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ * JB * ((X * Byᵀ).map (cA σ))ᵀ * JAᵀ =
      -(X * βᵀ * (((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * T0)ᵀ * JB * By.map (cA σ)) * (X.map (cA σ))ᵀ * JAᵀ) := by
    rw [Matrix.map_mul, Matrix.transpose_mul, ← Matrix.transpose_map, Matrix.transpose_transpose, Matrix.transpose_mul]
    simp only [Matrix.neg_mul, Matrix.mul_assoc]
  rw [e1, hf, Matrix.mul_one, Matrix.trace_neg, neg_one_mul, neg_neg, ← Matrix.trace_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc]
  rw [Matrix.mul_assoc (JA * X.map (cA σ)) β Xᵀ, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end PositivityTheory.SiegelWeilFormula.Tpar

end
