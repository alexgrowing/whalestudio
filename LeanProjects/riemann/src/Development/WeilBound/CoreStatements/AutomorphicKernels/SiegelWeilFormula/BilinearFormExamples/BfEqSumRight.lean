import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SDarb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeOfSig

set_option linter.unusedSectionVars false

noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inclR_eq (e : E) : inclR (F := F) (AF F) e = (1 : AF F) ⊗ₜ[F] e := rfl

theorem trace_inclR [FiniteDimensional F E] (e : E) :
    Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem cA_cA {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) (z : AE F E) : cA σ (cA σ z) = z := by
  have : (cA σ).comp (cA σ) = AlgHom.id (AF F) (AE F E) := by
    apply Algebra.TensorProduct.ext'
    intro a e
    simp [cA, hσ]
  exact congrArg (fun f : AE F E →ₐ[AF F] AE F E => f z) this

def cAe {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) : AE F E ≃ₐ[AF F] AE F E :=
  AlgEquiv.ofAlgHom (cA σ) (cA σ) (AlgHom.ext (cA_cA hσ)) (AlgHom.ext (cA_cA hσ))

theorem trace_cA {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) (z : AE F E) :
    Algebra.trace (AF F) (AE F E) (cA σ z) = Algebra.trace (AF F) (AE F E) z :=
  Algebra.trace_eq_of_algEquiv (cAe hσ) z

theorem incM_mul {a b c : Type} [Fintype b] (x : Matrix a b E) (y : Matrix b c E) :
    incM F (x * y) = incM F x * incM F y := Matrix.map_mul

theorem incM_transpose {a b : Type} (x : Matrix a b E) : incM F xᵀ = (incM F x)ᵀ := (Matrix.transpose_map).symm

theorem map_cA_incM {σ : E →ₐ[F] E} {a b : Type} (x : Matrix a b E) : (incM F x).map (cA σ) = incM F (x.map σ) := by
  ext i j; rfl

variable {m n : ℕ}

theorem sum_crdB (bs : Module.Basis (Fin 2) F E) (Z : Mx F E m n) : ∑ k, crdB bs Z k • Ek bs k = Z := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Ek, Matrix.single_apply, smul_ite, smul_zero, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp only [and_self, if_true, crdB]
    conv_rhs => rw [← (Algebra.TensorProduct.basis (AF F) bs).sum_repr (Z i j)]
    simp [Algebra.TensorProduct.basis_apply]
  · intro j' _ h; simp [h]
  · simp
  · intro i' _ h; simp [h]
  · simp

def BfR (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (X : Mx F E m n) : Mx F E m n →ₗ[AF F] AF F where
  toFun Z := Bf σ J X Z
  map_add' Z Z' := by
    simp only [Bf, Matrix.map_add _ (map_add (cA σ)), Matrix.mul_add, Matrix.trace_add, map_add]
  map_smul' c Z := by
    have : (c • Z).map (cA σ) = c • Z.map (cA σ) := by ext i j; simp [map_smul]
    simp only [Bf, this, Matrix.mul_smul, Matrix.trace_smul, map_smul, RingHom.id_apply]

def BfL (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (Z : Mx F E m n) : Mx F E m n →ₗ[AF F] AF F where
  toFun X := Bf σ J X Z
  map_add' X X' := by
    simp only [Bf, Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add, map_add]
  map_smul' c X := by
    simp only [Bf, Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul, map_smul, RingHom.id_apply]

theorem Bf_eq_sum_right (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E) (X Z : Mx F E m n) :
    Bf σ J X Z = ∑ k, crdB bs Z k * Bf σ J X (Ek bs k) := by
  conv_lhs => rw [← sum_crdB bs Z]
  change BfR σ J X _ = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

theorem Bf_eq_sum_left (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E) (X Z : Mx F E m n) :
    Bf σ J X Z = ∑ k, crdB bs X k * Bf σ J (Ek bs k) Z := by
  conv_lhs => rw [← sum_crdB bs X]
  change BfL σ J Z _ = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

end PositivityTheory.SiegelWeilFormula.Ldexa
