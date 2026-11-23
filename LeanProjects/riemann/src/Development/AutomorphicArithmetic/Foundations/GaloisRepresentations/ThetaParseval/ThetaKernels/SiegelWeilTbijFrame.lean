import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.SySmulRight
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.TBij
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
section Gen
variable {R E' : Type} [CommRing R] [CommRing E'] [Algebra R E'] (c : E' →ₐ[R] E') {α β : Type} [Fintype α]
  [DecidableEq α] [Fintype β] [DecidableEq β]
end Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace Adp
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
abbrev _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) → Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) → AF F :=
  symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J))
abbrev _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := incM F d.b.1.toCols₂
abbrev _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w' = om (d.dd.e w) (d.dd.e w') :=
  d.dd.form w w'
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_add_left (w₁ w₂ w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (w₁ + w₂) w' = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w₁ w' + _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w₂ w' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq, map_add, om, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  ring
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_add_right (w w₁ w₂ : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w (w₁ + w₂) = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w₁ + _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w₂ := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq, map_add, om, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  ring
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_smul_right (a : AF F) (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w (a • w') = a * _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq, map_smul, om, Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_sum_left {ι : Type} (s : Finset ι) (a : ι → AF F) (v : ι → Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E))
    (w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (∑ i ∈ s, a i • v i) w' = ∑ i ∈ s, a i * _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (v i) w' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq, map_sum, map_smul, om, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, sum_dotProduct,
    dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_antisymm (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w' = -_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w' w := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq, om]
  ring
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_diag (Z Z' : Matrix (Fin d.m) (Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ) (Z' * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ) = 0 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy, symp]
  rw [hTens_outer _ _ _ _ _ _ _ (isLagr_diagCols (cA σ) (incM F d.Y.J)).1, mul_zero, map_zero]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.frame_iso : (d.b.1.toCols₂)ᵀ * dbl d.Y.J * d.b.1.toCols₂.map σ = 0 := by
  obtain ⟨ε, h⟩ := d.ok.frame.1
  have h2 := congrArg Matrix.toBlocks₂₂ h
  rw [Matrix.toBlocks_fromBlocks₂₂] at h2
  rw [← h2]
  ext i j
  simp [Matrix.toBlocks₂₂, Matrix.mul_apply, Matrix.toCols₂]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_frame (X X' : Matrix (Fin d.m) (Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (X * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) (X' * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) = 0 := by
  have h : (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ * dbl (incM F d.Y.J) * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d).map (cA σ) = 0 := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy, cA_incM, ← incM_dbl, ← incM_transpose, ← incM_mul, ← incM_mul, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.frame_iso, incM_zero']
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy, symp]
  rw [hTens_outer _ _ _ _ _ _ _ h, mul_zero, map_zero]
def _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : Matrix (Fin d.m) (Fin d.n) (AE F E) :=
  (w * (incM F (d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1)ᵀ).toCols₂
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_add (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d (w + w') = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w + _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w' := by
  ext i j; simp [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs, Matrix.add_mul, Matrix.toCols₂]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_smul (a : AF F) (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d (a • w) = a • _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w := by
  ext i j; simp [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs, Matrix.smul_mul, Matrix.toCols₂]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.decomp (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    ∃ Z : Matrix (Fin d.m) (Fin d.n) (AE F E), w = Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ + _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ := by
  obtain ⟨t, ht⟩ := d.ok.frame.2
  set V := w * (incM F (d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1)ᵀ with hV
  have h1 : w = V * (incM F d.b.1)ᵀ := by
    rw [hV, Matrix.mul_assoc, ← Matrix.transpose_mul, ← incM_mul, Units.mul_inv, incM_one', Matrix.transpose_one,
      Matrix.mul_one]
  have h2 : incM F d.b.1 = Matrix.fromCols (incM F d.b.1.toCols₁) (incM F d.b.1.toCols₂) := by
    ext i (j | j) <;> rfl
  refine ⟨V.toCols₁ * (incM F t.1)ᵀ, ?_⟩
  have h3 : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w = V.toCols₂ := rfl
  rw [h3]
  conv_lhs => rw [h1, h2, ← Matrix.fromCols_toCols V]
  have ht' : incM F d.b.1.toCols₁ = @HMul.hMul (Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))
      (Matrix (Fin d.n) (Fin d.n) (AE F E)) (Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))
      Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (diagCols (Fin d.n)) (incM F t.1) := by
    rw [ht, ← incM_diagCols (F := F) (E := E)]
    exact incM_mul _ _
  rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows, ht', Matrix.transpose_mul, ← Matrix.mul_assoc]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_frame (X : Matrix (Fin d.m) (Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d (X * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) = X := by
  have h1 : incM F (d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1 * _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).toCols₂ := by
    have : (d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1 * d.b.1.toCols₂ = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E).toCols₂ := by
      rw [← Units.inv_mul d.b]
      ext i j; simp [Matrix.mul_apply, Matrix.toCols₂]
    rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy, ← incM_mul, this]
    ext i j; simp [incM, Matrix.toCols₂, Matrix.one_apply]
  rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs, Matrix.mul_assoc, ← Matrix.transpose_mul, h1]
  ext i j
  simp [Matrix.toCols₂, Matrix.mul_apply, Matrix.one_apply]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_split (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w' = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w' - _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w' * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w := by
  obtain ⟨Z, hZ⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.decomp d w
  obtain ⟨Z', hZ'⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.decomp d w'
  have a1 : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w' = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ) w' + _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w' := by
    conv_lhs => rw [hZ]
    rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_add_left]
  have a2 : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ) w' = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ) (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w' * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) := by
    conv_lhs => rw [hZ']
    rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_add_right, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_diag, zero_add]
  have a3 : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w' * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w' * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ) := by
    conv_lhs => rw [hZ]
    rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_add_right, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_frame, add_zero]
  rw [a1, a2, a3, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_antisymm d (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ)]
  ring
end Adp
end PositivityTheory.SiegelWeilFormula.TBij
end
end
