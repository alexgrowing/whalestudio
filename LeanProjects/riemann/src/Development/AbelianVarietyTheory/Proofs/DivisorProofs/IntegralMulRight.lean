import Development.AbelianVarietyTheory.Definitions.Divisors.AnisoClauseOfFirstTerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModule
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RightMulJac

theorem integral_mul_right : ∀ (D : D7) (t n : ℕ) (μ₁ : Measure (Mx D t n)) (𝓕₁ : Set (Mx D t n)),
    IsCovolOne (ratMx D t n) μ₁ 𝓕₁ →
    ∀ (a : GL (Fin n) (AE D)) (f : Mx D t n → ℂ),
      ∫ x, f (x ⬝ a.1) ∂μ₁ = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(t : ℂ)) * ∫ x, f x ∂μ₁ := by
  intro D t n μ₁ 𝓕₁ hμ a f
  haveI : μ₁.IsAddHaarMeasure := hμ.1
  haveI : BorelSpace (Mx D t n) := ⟨rfl⟩
  have hkey := GlobalTheory.ModuLR.modu_lrMul D t n μ₁ hμ.1 1 a
  simp only [map_one, one_pow, one_mul, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mul, ENNReal.coe_one] at hkey
  set c : ℝ≥0 := absA D (Matrix.GeneralLinearGroup.det a) with hc
  have hc0 : c ≠ 0 := by
    exact ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map (absA D)).ne_zero
  have hcont : Continuous fun u : Mx D t n => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) a.val : Mx D t n) := continuous_id.matrix_mul continuous_const
  have hcont' : Continuous fun u : Mx D t n => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) (a⁻¹).val : Mx D t n) := continuous_id.matrix_mul continuous_const
  let e : Mx D t n ≃ₜ Mx D t n :=
    { toFun := fun u => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) a.val : Mx D t n)
      invFun := fun u => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) (a⁻¹).val : Mx D t n)
      left_inv := fun u => by simp [Matrix.mul_assoc]
      right_inv := fun u => by simp [Matrix.mul_assoc]
      continuous_toFun := hcont
      continuous_invFun := hcont' }
  have hemb : MeasurableEmbedding (fun u : Mx D t n => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) a.val : Mx D t n)) := e.measurableEmbedding
  have hmap : μ₁.map (fun u : Mx D t n => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) a.val : Mx D t n)) = ((c : ENNReal) ^ t)⁻¹ • μ₁ := by
    conv_rhs => rw [hkey]
    rw [smul_smul, ENNReal.inv_mul_cancel (by simp [hc0]) (by simp), one_smul]
  rw [show (∫ x, f (x ⬝ a.1) ∂μ₁) = ∫ x, f ((fun u : Mx D t n => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) a.val : Mx D t n)) x) ∂μ₁ from rfl,
    ← hemb.integral_map, hmap, integral_smul_measure]
  rw [Complex.real_smul, npow]
  congr 1
  rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.coe_toReal,
    show (-(t : ℂ)) = ((-(t : ℝ) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (NNReal.coe_nonneg c), Real.rpow_neg (NNReal.coe_nonneg c), Real.rpow_natCast]

end GlobalTheory.RightMulJac

end
