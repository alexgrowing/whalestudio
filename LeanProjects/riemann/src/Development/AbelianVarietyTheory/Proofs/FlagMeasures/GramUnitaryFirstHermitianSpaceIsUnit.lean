import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGram
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryStabiliserOrthogonalSummand
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Transfer
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.St.gramN_unitary_isUnit : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, (y₀.map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * y₀ = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm → ∃ g : GL (Fin (D.R.N 0)) D.host.E, (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = y₀.map X.ιE := by
  intro D X u wt hW y₀ hy
  obtain ⟨Q, Qi, G', hQQi, hQiQ, -, -, -, -, -, hM⟩ := GlobalTheory.St.qFrame_basis_gram D X u wt hW
  set G := (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm with hG
  have hJ := X.B.I.J_det
  have hJJ : X.B.I.J * X.B.I.J⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hJ)
  have h1 : (Q.map (starRingEnd X.B.I.E))ᵀ * (Qi.map (starRingEnd X.B.I.E))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hQiQ]; simp
  have hdetM : IsUnit (Matrix.fromBlocks G 0 0 G').det := by
    rw [← hM]
    apply Matrix.isUnit_det_of_right_inverse (B := Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ)
    calc (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q * (Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ)
        = (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * (Q * Qi) * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = (Q.map (starRingEnd X.B.I.E))ᵀ * (X.B.I.J * X.B.I.J⁻¹) * (Qi.map (starRingEnd X.B.I.E))ᵀ := by
          rw [hQQi]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hJJ, Matrix.mul_one, h1]
  rw [Matrix.det_fromBlocks_zero₂₁] at hdetM
  have hGdet : G.det ≠ 0 := (isUnit_of_mul_isUnit_left hdetM).ne_zero
  have hy0 : y₀.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hy
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact hGdet this.symm
  have hd : (y₀.map X.ιE).det = X.ιE y₀.det := by
    simpa using (RingHom.map_det X.ιE.toRingHom y₀).symm
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (y₀.map X.ιE) ?_, rfl⟩
  rw [hd]; exact (map_ne_zero X.ιE).mpr hy0
