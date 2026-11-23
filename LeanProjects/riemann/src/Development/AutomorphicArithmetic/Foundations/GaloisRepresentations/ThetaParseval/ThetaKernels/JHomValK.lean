import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.UnitaryConjIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def jHom_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) :
    G2 σ Y →* GL (Fin d.n ⊕ Fin d.n) (AE F E) :=
  (MulAut.conj (bA d.b)).toMonoidHom.comp ((blkGL h).comp
    ((MulAut.conj (bA (F := F) b)⁻¹).toMonoidHom.comp (UG (cA σ) (dbl (incM F Y.J))).subtype))
theorem jHom_val_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (g : G2 σ Y) :
    (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1 = incM F d.b.1 * blk h (inFrame b g) 1 * incM F (d.b⁻¹).1 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_subtype,
    Units.val_mul, bA_val, bA_inv_val, blkGL, Units.coe_map, blkHom, MonoidHom.coe_mk, OneHom.coe_mk, inFrame_eq]
theorem jHom_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ)
    (e1 : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε) (e2 : b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε) (g : G2 σ Y) :
    _root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
  have hG1 : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom = incM F (jeps d.n ε) := by
    rw [← e1, ← incM_gram, incM_dbl]; rfl
  have hG2 : (incM F b.1)ᵀ * dbl (incM F Y.J) * (incM F b.1).map (cA σ).toRingHom = incM F (jeps n ε) := by
    rw [← e2, ← incM_gram, incM_dbl]; rfl
  have hg : (g.1.1)ᵀ * dbl (incM F Y.J) * (g.1.1).map (cA σ).toRingHom = dbl (incM F Y.J) := g.2
  have hM := (unitary_conj_iff (cA σ).toRingHom _ _ _ _ g.1.1 (incM_mul_inv b) (incM_inv_mul b) hG2).1 hg
  rw [← inFrame_eq] at hM
  show (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1ᵀ * dbl (incM F d.Y.J) * (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1.map (cA σ).toRingHom = dbl (incM F d.Y.J)
  rw [unitary_conj_iff (cA σ).toRingHom _ _ _ _ _ (incM_mul_inv d.b) (incM_inv_mul d.b) hG1, _root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_val_k]
  have eQP : incM F (d.b⁻¹).1 * (incM F d.b.1 * blk h (inFrame b g) 1 * incM F (d.b⁻¹).1) * incM F d.b.1 =
      blk h (inFrame b g) 1 := by
    simp only [← Matrix.mul_assoc, incM_inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, incM_inv_mul, Matrix.mul_one]
  rw [eQP, incM_jeps, jepsR_blk h, ← incM_jeps, ← incM_jeps, blk_transpose, blk_map _ _ _ _ (map_zero _), blk_mul,
    blk_mul, hM]
  congr 1
  simp [Matrix.map_one _ (map_zero _) (map_one _)]
end PositivityTheory.SiegelWeilFormula.Ald
end
end
