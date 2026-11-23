import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.BlockMatrixDiagonalOneEqOne
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawB

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Matrix
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

theorem alg_id (Z R : ℂ) (hZ : Z ≠ 0) (hR : R ≠ 0) (k j : ℤ) (p q m : ℕ) (hm : p + q = m) (hj : k - m = j + j) :
    (Z / R) ^ k * R ^ (m : ℤ) = (Z * (Z / R ^ 2)) ^ (k - j) * ((Z / R ^ 2) ^ (-(p : ℤ)) * (Z / R ^ 2) ^ (-(q : ℤ))) := by
  have hk : k = (m : ℤ) + j + j := by omega
  have hkj : k - j = (m : ℤ) + j := by omega
  have hpq : -(p : ℤ) + -(q : ℤ) = -(m : ℤ) := by omega
  rw [← zpow_add₀ (div_ne_zero hZ (pow_ne_zero 2 hR)), hpq, hkj, hk]
  have hR2 : (R ^ 2 : ℂ) = R * R := by ring
  rw [hR2]
  simp only [div_eq_mul_inv, mul_zpow, _root_.inv_zpow, zpow_add₀ hZ, zpow_add₀ hR, _root_.zpow_neg, zpow_natCast, inv_inv, mul_inv]
  have h1 : Z ^ m ≠ 0 := pow_ne_zero _ hZ
  have h2 : R ^ m ≠ 0 := pow_ne_zero _ hR
  have h3 : Z ^ j ≠ 0 := zpow_ne_zero _ hZ
  have h4 : R ^ j ≠ 0 := zpow_ne_zero _ hR
  field_simp
  ring_nf
  rw [inv_pow]
  field_simp

end PositivityTheory.Rg.Sw.Glob.LocLawH
