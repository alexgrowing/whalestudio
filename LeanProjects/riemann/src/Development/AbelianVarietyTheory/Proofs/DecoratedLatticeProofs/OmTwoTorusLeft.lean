import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepChainStepMatrixCoefficientTwisted
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.TorusLeft

theorem sum_indic {D' : Type} [Fintype D'] [DecidableEq D'] (s : Finset D') : ∑ i, indic s i = (s.card : ℤ) := by
  simp [indic]

theorem zpow_rpow_half (q : ℝ) (hq : 0 ≤ q) (n m : ℕ) :
    ((q ^ (-(n : ℤ)) : ℝ) ^ (-(m : ℝ) / 2)) = (Real.sqrt q) ^ (n * m) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq, ← Real.rpow_intCast, ← Real.rpow_mul hq]
  congr 1
  push_cast; ring

theorem omTwo_torusLeft : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ μS μT : kˣ →* ℂˣ), IsUnram (μS * ξ⁻¹) → ∀ (s : Finset D') (j : GL (A ⊕ D') k), j ∈ parahoric k A D' → ∀ (u : Matrix (A ⊕ D') (A ⊕ D) k → ℂ) (y : Matrix (A ⊕ D') (A ⊕ D) k), omTwo μS μT (1 : GL (A ⊕ D) k) (j * mtor ϖ (indic s)) u y = (μS ϖ : ℂ) ^ s.card * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (s.card * (Fintype.card A + Fintype.card D)) * (ξ (GeneralLinearGroup.det j) : ℂ) * u (((j * mtor ϖ (indic s))⁻¹ : GL (A ⊕ D') k).1 * y) := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ ξ μS μT hu s j hj u y
  have hKO : j ∈ KO k (A ⊕ D') := (mem_parahoric.1 hj).1
  have hnj : nabs k (GeneralLinearGroup.det j) = 1 := nabs_det_of_mem_KO hKO
  have hvj : valuation k ((GeneralLinearGroup.det j : kˣ) : k) = 1 := (nabs_eq_one_iff _).1 hnj
  have hξ : μS (GeneralLinearGroup.det j) = ξ (GeneralLinearGroup.det j) := by
    have := hu _ hvj
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at this
    exact this
  have hdm : GeneralLinearGroup.det (mtor ϖ (indic s) : GL (A ⊕ D') k) = ϖ ^ (s.card : ℤ) := by
    rw [GlobalTheory.ChainStepCoef.det_mtor, sum_indic]
  have hnm : nabs k (GeneralLinearGroup.det (mtor ϖ (indic s) : GL (A ⊕ D') k)) = (resCard k : ℝ) ^ (-(s.card : ℤ)) := by
    rw [GlobalTheory.ChainStepCoef.nabs_det_mtor hϖ, sum_indic]
  have hnh : nabs k (GeneralLinearGroup.det (j * mtor ϖ (indic s))) = (resCard k : ℝ) ^ (-(s.card : ℤ)) := by
    rw [map_mul, nabs_mul, hnj, hnm, one_mul]
  have hμh : μS (GeneralLinearGroup.det (j * mtor ϖ (indic s))) = ξ (GeneralLinearGroup.det j) * μS ϖ ^ s.card := by
    rw [map_mul, map_mul, hξ, hdm, zpow_natCast, map_pow]
  have hq : ((nabs k (GeneralLinearGroup.det (j * mtor ϖ (indic s))) ^ (-(Fintype.card (A ⊕ D) : ℝ) / 2) : ℝ) : ℂ)
      = ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (s.card * (Fintype.card A + Fintype.card D)) := by
    rw [hnh, ← Fintype.card_sum, zpow_rpow_half _ (Nat.cast_nonneg _)]
    push_cast; rfl
  have key : (((μS * μT⁻¹) (GeneralLinearGroup.det (j * mtor ϖ (indic s))) : ℂˣ) : ℂ) *
      (((μT⁻¹ (GeneralLinearGroup.det (j * mtor ϖ (indic s))))⁻¹ : ℂˣ) : ℂ) =
      (μS (GeneralLinearGroup.det (j * mtor ϖ (indic s))) : ℂ) := by
    rw [← Units.val_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, inv_inv, inv_mul_cancel_right]
  simp only [omTwo, om, Pi.smul_apply, smul_eq_mul, map_one, Units.val_one, one_mul, nabs_one, Real.one_rpow, Complex.ofReal_one, mul_one, Matrix.mul_one]
  rw [hq, ← mul_assoc, ← mul_assoc, key, hμh, Units.val_mul, Units.val_pow_eq_pow_val]
  ring

end GlobalTheory.TorusLeft
