import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SDarb
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.BfENondeg
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.TraceIntMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeOfSig

set_option linter.unusedSectionVars false

noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {m n : ℕ}

def Gm (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E) :
    Matrix (Fin m × Fin n × Fin 2) (Fin m × Fin n × Fin 2) F :=
  LinearMap.BilinForm.toMatrix (bs.matrix (Fin m) (Fin n)) (BfE σ J)

theorem Gm_det [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (J : Matrix (Fin m) (Fin m) E)
    (hJ : J.det ≠ 0) (bs : Module.Basis (Fin 2) F E) : (Gm (n := n) σ J bs).det ≠ 0 :=
  (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero _).1 (BfE_nondeg σ hσ J hJ)

theorem Bf_Ek_Ek [FiniteDimensional F E] (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E)
    (k k' : Fin m × Fin n × Fin 2) : Bf σ J (Ek bs k) (Ek bs k') = algebraMap F (AF F) (Gm σ J bs k k') := by
  obtain ⟨i, j, l⟩ := k
  obtain ⟨i', j', l'⟩ := k'
  have hE : ∀ (a : Fin m) (b : Fin n) (c : Fin 2), Ek bs (a, b, c) = incM F (Matrix.single a b (bs c)) := by
    intro a b c
    ext x y
    by_cases hx : a = x <;> by_cases hy : b = y <;> simp [Ek, incM, Matrix.single_apply, inclR, hx, hy]
  have hc : ∀ M : Matrix (Fin m) (Fin n) E, (incM F M).map (cA σ) = incM F (M.map σ) := by
    intro M
    ext x y
    simp [incM, cA, inclR]
  have htr : ∀ M : Matrix (Fin m) (Fin n) E, (incM F M)ᵀ = incM F Mᵀ := by
    intro M
    ext x y
    rfl
  have ht : ∀ M : Matrix (Fin n) (Fin n) E, (incM F M).trace = inclR (F := F) (E := E) (AF F) M.trace := by
    intro M
    rw [incM, AddMonoidHom.map_trace]
  rw [Gm, LinearMap.BilinForm.toMatrix_apply, Module.Basis.matrix_apply, Module.Basis.matrix_apply, Bf, hE, hE, hc,
    htr, ← incM_mul, ← incM_mul, ht, trace_inclR']
  rfl

def bM (bs : Module.Basis (Fin 2) F E) : Module.Basis (Fin m × Fin n × Fin 2) (AF F) (Mx F E m n) :=
  (Algebra.TensorProduct.basis (AF F) bs).matrix (Fin m) (Fin n)

theorem bM_apply (bs : Module.Basis (Fin 2) F E) (k : Fin m × Fin n × Fin 2) : bM bs k = Ek bs k := by
  obtain ⟨i, j, l⟩ := k
  simp [bM, Ek, Algebra.TensorProduct.basis_apply]

theorem bM_repr (bs : Module.Basis (Fin 2) F E) (X : Mx F E m n) (k : Fin m × Fin n × Fin 2) :
    (bM bs).repr X k = crdB bs X k := by
  obtain ⟨i, j, l⟩ := k
  have hinj : Function.Injective (Prod.map id ⇑(Equiv.sigmaEquivProd (Fin n) (Fin 2)) ∘
      ⇑(Equiv.sigmaEquivProd (Fin m) (Σ _ : Fin n, Fin 2))) :=
    (Function.injective_id.prodMap (Equiv.injective _)).comp (Equiv.injective _)
  simp [bM, Module.Basis.matrix, crdB, Pi.basis_repr]
  rw [show ((i, j, l) : Fin m × Fin n × Fin 2) = (Prod.map id ⇑(Equiv.sigmaEquivProd (Fin n) (Fin 2)) ∘
      ⇑(Equiv.sigmaEquivProd (Fin m) (Σ _ : Fin n, Fin 2))) ⟨i, ⟨j, l⟩⟩ from rfl,
    Finsupp.mapDomain_apply hinj, Pi.basis_repr, Pi.basis_repr]
  rfl

theorem incM_one {ι : Type} [Fintype ι] [DecidableEq ι] : incM F (1 : Matrix ι ι E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

def eQ (b : GL (Fin n ⊕ Fin n) E) : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E) ≃ₗ[AF F] Mx F E m n × Mx F E m n :=
  LinearEquiv.ofLinear
    { toFun := fun w => ((w * (incM F (b⁻¹).1)ᵀ).toCols₁, (w * (incM F (b⁻¹).1)ᵀ).toCols₂)
      map_add' := fun w w' => by rw [Matrix.add_mul]; rfl
      map_smul' := fun c w => by rw [Matrix.smul_mul]; rfl }
    { toFun := fun p => p.1 * (incM F b.1.toCols₁)ᵀ + p.2 * (incM F b.1.toCols₂)ᵀ
      map_add' := fun p p' => by simp [Matrix.add_mul]; abel
      map_smul' := fun c p => by simp [Matrix.smul_mul, smul_add] }
    (by
      refine LinearMap.ext fun p => ?_
      obtain ⟨Z, X⟩ := p
      have h1 : (incM F b.1)ᵀ * (incM F (b⁻¹).1)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, ← incM_mul, Units.inv_mul, incM_one, Matrix.transpose_one]
      show (((Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ) * (incM F (b⁻¹).1)ᵀ).toCols₁,
        ((Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ) * (incM F (b⁻¹).1)ᵀ).toCols₂) = (Z, X)
      rw [show Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ = Matrix.fromCols Z X * (incM F b.1)ᵀ by
        rw [incM_b, Matrix.fromCols_mul_fromRows], Matrix.mul_assoc, h1, Matrix.mul_one]
      simp)
    (by
      refine LinearMap.ext fun w => ?_
      have h1 : (incM F (b⁻¹).1)ᵀ * (incM F b.1)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, ← incM_mul, Units.mul_inv, incM_one, Matrix.transpose_one]
      show (w * (incM F (b⁻¹).1)ᵀ).toCols₁ * (incM F b.1.toCols₁)ᵀ + (w * (incM F (b⁻¹).1)ᵀ).toCols₂ * (incM F b.1.toCols₂)ᵀ = w
      rw [← Matrix.fromCols_mul_fromRows, ← incM_b, Matrix.fromCols_toCols, Matrix.mul_assoc, h1, Matrix.mul_one])

theorem eQ_symm_apply (b : GL (Fin n ⊕ Fin n) E) (Z X : Mx F E m n) :
    (eQ b).symm (Z, X) = Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ := rfl

theorem eQ_frame (b : GL (Fin n ⊕ Fin n) E) (Z X : Mx F E m n) :
    eQ b (Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ) = (Z, X) := by
  rw [← eQ_symm_apply, LinearEquiv.apply_symm_apply]

end PositivityTheory.SiegelWeilFormula.Ldexa
