import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.IsHaarMeasureDoubledGroup
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.PhiEqZeroIff
import GroundTheory.GlobalFields.Adele.Compact

noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.EisBL.NilAlg

namespace GlobalTheory.EisBL.DoubledUnipotentRadical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem matrixRep_mul {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} (a b : G2 σ Y) : mat2 (a * b) = mat2 a * mat2 b := rfl

omit [NumberField E] in
theorem matrixRep_one {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} : mat2 (1 : G2 σ Y) = 1 := rfl

omit [NumberField E] in
theorem matrix_inv_mul_doubled {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} (a : G2 σ Y) : mat2 a⁻¹ * mat2 a = 1 :=
  Units.inv_mul a.1

omit [NumberField E] in
theorem diagCols_eq {n : ℕ} : diagCols (E := AE F E) (Fin n) =
    Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
  unfold diagCols; rfl

omit [NumberField E] in
theorem unip_iff {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} (g : G2 σ Y) :
    ((mat2 g - 1) * diagCols (E := AE F E) (Fin n) = 0 ∧
      Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) * (mat2 g - 1) = 0) ↔
      ∃ X, mat2 g = blk X := by
  rw [diagCols_eq]; exact unip_iff_blk (mat2 g)

variable (σ) in

def nil2 {n : ℕ} (Y : Spc F E n) : Subgroup (G2 σ Y) where
  carrier := {g | (mat2 g - 1) * diagCols (Fin n) = 0 ∧
    Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) * (mat2 g - 1) = 0}
  one_mem' := (unip_iff (1 : G2 σ Y)).2 ⟨0, by rw [matrixRep_one, blk_zero]⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨X, hX⟩ := (unip_iff a).1 ha
    obtain ⟨Z, hZ⟩ := (unip_iff b).1 hb
    exact (unip_iff (a * b)).2 ⟨X + Z, by rw [matrixRep_mul, hX, hZ, blk_mul]⟩
  inv_mem' := by
    intro a ha
    obtain ⟨X, hX⟩ := (unip_iff a).1 ha
    refine (unip_iff a⁻¹).2 ⟨-X, ?_⟩
    calc mat2 a⁻¹ = mat2 a⁻¹ * (blk X * blk (-X)) := by rw [blk_mul, add_neg_cancel, blk_zero, Matrix.mul_one]
      _ = (mat2 a⁻¹ * mat2 a) * blk (-X) := by rw [hX, Matrix.mul_assoc]
      _ = blk (-X) := by rw [matrix_inv_mul_doubled, Matrix.one_mul]

def eltA (σ : E →ₐ[F] E) {n : ℕ} (Y : Spc F E n) (Z : Matrix (Fin n) (Fin n) (AE F E))
    (hZ : phi (cA σ).toRingHom (incM F Y.J) Z = 0) : G2 σ Y :=
  ⟨⟨blk Z, blk (-Z), by rw [blk_mul, add_neg_cancel, blk_zero], by rw [blk_mul, neg_add_cancel, blk_zero]⟩,
    (blk_form_iff _ _ _).2 hZ⟩

omit [NumberField E] in
theorem cA_inclR (σ : E →ₐ[F] E) (x : E) :
    cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) = (1 : AF F) ⊗ₜ[F] σ x
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

omit [NumberField E] in
theorem cA_cA (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ
      (Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ (a ⊗ₜ[F] x)) = a ⊗ₜ[F] x
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end GlobalTheory.EisBL.DoubledUnipotentRadical
