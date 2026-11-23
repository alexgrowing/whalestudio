import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdeleAt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder

namespace GlobalTheory.KJReal

variable {D : D7}

theorem detPlus_one_one {m n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.WeilParts.detPlus 1 1 a b = b.det ^ n * a.det ^ m := by
  unfold GlobalTheory.WeilParts.detPlus
  have e2 : (1 + 1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) = (2 : ℂ) • 1 := by
    rw [two_smul]
  rw [Matrix.transpose_one, Matrix.one_kronecker_one, sub_self, smul_zero, add_zero, e2, Matrix.smul_mul,
    Matrix.one_mul, smul_smul, show (1 / 2 * 2 : ℂ) = 1 by norm_num, one_smul, Matrix.det_kronecker,
    Matrix.det_transpose, Fintype.card_fin, Fintype.card_fin]

theorem exp_identity (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (e mS mT : ℤ) (nS nT : ℕ) (hS : (nS : ℤ) = mS + mS)
    (hT : (nT : ℤ) = mT + mT) :
    (a ^ (e - mT))⁻¹ * b ^ (e - mS) * (b ^ nS * a⁻¹ ^ nT) = a ^ (-e - mT) * b ^ (e + mS) := by
  rw [inv_pow, ← zpow_natCast b, ← zpow_natCast a, ← zpow_neg a, ← zpow_neg a]
  calc (a ^ (-(e - mT)) * b ^ (e - mS) * (b ^ (nS : ℤ) * a ^ (-(nT : ℤ))))
      = a ^ (-(e - mT)) * a ^ (-(nT : ℤ)) * (b ^ (e - mS) * b ^ (nS : ℤ)) := by ring
    _ = a ^ (-(e - mT) + -(nT : ℤ)) * b ^ (e - mS + (nS : ℤ)) := by rw [← zpow_add₀ ha, ← zpow_add₀ hb]
    _ = a ^ (-e - mT) * b ^ (e + mS) := by
      congr 2
      · rw [hT]; ring
      · rw [hS]; ring

end GlobalTheory.KJReal

namespace GlobalTheory.KJReal

end GlobalTheory.KJReal
