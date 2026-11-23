import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FiniteCovolume.Reindex

open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def reGL (e : ι ≃ κ) : GL ι ℂ →* GL κ ℂ :=
  Units.map (Matrix.reindexRingEquiv ℂ e).toMonoidHom

theorem coe_reGL (e : ι ≃ κ) (g : GL ι ℂ) :
    ((reGL e g : GL κ ℂ) : Matrix κ κ ℂ) = reindex e e (g : Matrix ι ι ℂ) := rfl

theorem reGL_symm_reGL (e : ι ≃ κ) (g : GL ι ℂ) : reGL e.symm (reGL e g) = g := by
  ext i j
  simp [coe_reGL, Matrix.reindex_apply]

theorem reGL_reGL_symm (e : ι ≃ κ) (g : GL κ ℂ) : reGL e (reGL e.symm g) = g := by
  ext i j
  simp [coe_reGL, Matrix.reindex_apply]

theorem continuous_reGL (e : ι ≃ κ) : Continuous (reGL e) :=
  Units.continuous_map (continuous_id.matrix_reindex e e)

theorem reGL_mem_unitary (e : ι ≃ κ) (s : ℂ →+* ℂ) (H : Matrix ι ι ℂ) (g : GL ι ℂ) :
    reGL e g ∈ unitaryGroupMatrix s (reindex e e H) ↔ g ∈ unitaryGroupMatrix s H := by
  rw [mem_unitaryGroupMatrix, mem_unitaryGroupMatrix, coe_reGL]
  have : ((reindex e e (g : Matrix ι ι ℂ)).map s)ᵀ * reindex e e H * reindex e e (g : Matrix ι ι ℂ) =
      reindex e e (((g : Matrix ι ι ℂ).map s)ᵀ * H * (g : Matrix ι ι ℂ)) := by
    simp only [Matrix.reindex_apply]
    rw [← Matrix.submatrix_map, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv]
  rw [this, (reindex e e).injective.eq_iff]

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem gramAt_reindex (h : HermitianForm F E W) (v : Basis ι E W) (e : ι ≃ κ)
    (w : InfinitePlace E) : gramAt h (v.reindex e) w = reindex e e (gramAt h v w) := by
  ext i j
  simp [gramAt, Automorphic.gram_apply, Basis.reindex_apply, Matrix.reindex_apply]

theorem vecAt_reindex (v : Basis ι E W) (e : ι ≃ κ) (x : W) :
    vecAt (v.reindex e) x = fun w => vecAt v x w ∘ e.symm := by
  funext w i
  simp [vecAt]

variable [NumberField E]

def archReindex (h : HermitianForm F E W) (v : Basis ι E W) (e : ι ≃ κ) :
    archUnitary h v →* archUnitary h (v.reindex e) where
  toFun g := ⟨fun w => reGL e ((g : InfinitePlace E → GL ι ℂ) w), (Subgroup.mem_pi _).2 fun w _ => by
    rw [gramAt_reindex, reGL_mem_unitary]
    exact (Subgroup.mem_pi _).1 g.2 w trivial⟩
  map_one' := by
    ext w : 2
    simp
  map_mul' a b := by
    ext w : 2
    simp

def archReindexBack (h : HermitianForm F E W) (v : Basis ι E W) (e : ι ≃ κ) :
    archUnitary h (v.reindex e) →* archUnitary h v where
  toFun g := ⟨fun w => reGL e.symm ((g : InfinitePlace E → GL κ ℂ) w),
    (Subgroup.mem_pi _).2 fun w _ => by
      rw [← reGL_mem_unitary e, reGL_reGL_symm, ← gramAt_reindex]
      exact (Subgroup.mem_pi _).1 g.2 w trivial⟩
  map_one' := by
    ext w : 2
    simp
  map_mul' a b := by
    ext w : 2
    simp

theorem archReindexBack_archReindex (h : HermitianForm F E W) (v : Basis ι E W) (e : ι ≃ κ)
    (g : archUnitary h v) : archReindexBack h v e (archReindex h v e g) = g := by
  apply Subtype.ext
  funext w
  exact reGL_symm_reGL e _

theorem continuous_archReindexBack (h : HermitianForm F E W) (v : Basis ι E W) (e : ι ≃ κ) :
    Continuous (archReindexBack h v e) :=
  Continuous.subtype_mk (continuous_pi fun w =>
    (continuous_reGL e.symm).comp ((continuous_apply w).comp continuous_subtype_val)) _

theorem invApply_reindex {h : HermitianForm F E W} {v : Basis ι E W} (e : ι ≃ κ)
    (g : archUnitary h v) (y : InfinitePlace E → ι → ℂ) :
    invApply (archReindex h v e g) (fun w => y w ∘ e.symm) = fun w => invApply g y w ∘ e.symm := by
  funext w
  rw [invApply, invApply, ← map_inv]
  change (reindex e e _) *ᵥ (y w ∘ e.symm) = _
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Function.comp_assoc, Equiv.symm_symm,
    Equiv.symm_comp_self, Function.comp_id]

def majReindex {h : HermitianForm F E W} {v : Basis ι E W} (e : ι ≃ κ) (M : Majorant h v) :
    Majorant h (v.reindex e) where
  P w := Matrix.reindex e e (M.P w)
  posDef w := by
    rw [Matrix.reindex_apply]
    exact (M.posDef w).submatrix e.symm.injective
  siegel w := by
    rw [gramAt_reindex, Matrix.inv_reindex]
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    rw [M.siegel w]

theorem len_majReindex {h : HermitianForm F E W} {v : Basis ι E W} (e : ι ≃ κ)
    (M : Majorant h v) (y : InfinitePlace E → ι → ℂ) :
    (majReindex e M).len (fun w => y w ∘ e.symm) = M.len y := by
  unfold Majorant.len
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  change star (y w ∘ e.symm) ⬝ᵥ (Matrix.reindex e e (M.P w) *ᵥ (y w ∘ e.symm)) =
    star (y w) ⬝ᵥ (M.P w *ᵥ y w)
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Function.comp_assoc, Equiv.symm_symm,
    Equiv.symm_comp_self, Function.comp_id]
  simp only [dotProduct, Function.comp_apply, Pi.star_apply]
  exact Equiv.sum_comp e.symm (fun i => star (y w i) * (M.P w *ᵥ y w) i)

theorem len_invApply_reindex {h : HermitianForm F E W} {v : Basis ι E W} (e : ι ≃ κ)
    (M : Majorant h v) (g : archUnitary h v) (x : W) :
    (majReindex e M).len (invApply (archReindex h v e g) (vecAt (v.reindex e) x)) =
      M.len (invApply g (vecAt v x)) := by
  rw [vecAt_reindex, invApply_reindex, len_majReindex]

variable [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]

theorem archReindex_archEmbed (h : HermitianForm F E W) (v : Basis ι E W) (e : ι ≃ κ)
    (γ : h.unitaryGroup) : archReindex h v e (archEmbed h v γ) = archEmbed h (v.reindex e) γ := by
  apply Subtype.ext
  funext w
  ext i j
  change reindex e e ((Matrix.GeneralLinearGroup.map w.embedding
      (unitaryGroupEquivMatrix h v γ : GL ι E) : GL ι ℂ) : Matrix ι ι ℂ) i j =
    ((Matrix.GeneralLinearGroup.map w.embedding
      (unitaryGroupEquivMatrix h (v.reindex e) γ : GL κ E) : GL κ ℂ) : Matrix κ κ ℂ) i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.GeneralLinearGroup.map_apply]
  congr 1
  rw [unitaryGroupEquivMatrix_apply, unitaryGroupEquivMatrix_apply, LinearMap.toMatrix_apply,
    LinearMap.toMatrix_apply, Basis.reindex_apply, Basis.repr_reindex_apply]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume.Reindex
