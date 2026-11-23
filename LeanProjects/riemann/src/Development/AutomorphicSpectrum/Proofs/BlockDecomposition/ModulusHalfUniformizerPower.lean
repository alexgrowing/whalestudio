import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.WS

theorem mp_uniformizer_zpow_half (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (m : ℤ) :
    mp (Iwasawa.uniformizerUnit F ^ m) (1 / 2) = Spherical.sqrtQ F ^ (-m) := by
  set r : NNReal := NNReal.sqrt (Spherical.qF F : NNReal) with hr
  have hr2 : r ^ 2 = (Spherical.qF F : NNReal) := NNReal.sq_sqrt _
  have hmod : Measures.modulus (((Iwasawa.uniformizerUnit F ^ m : Fˣ)) : F) = (r ^ (-m)) ^ 2 := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, Iwasawa.coe_uniformizerUnit,
      Spherical.modulus_uniformizer, ← hr2, ← zpow_natCast r 2, ← zpow_natCast (r ^ (-m)) 2,
      ← _root_.zpow_neg, ← _root_.zpow_mul, ← _root_.zpow_mul]
    congr 1
    push_cast
    ring
  have hS : Spherical.sqrtQ F = ((r : ℝ) : ℂ) := rfl
  have ht : (0 : ℝ) ≤ ((r ^ (-m) : NNReal) : ℝ) := NNReal.coe_nonneg _
  have hbr : GroundTheory.LocalField.modulus (((Iwasawa.uniformizerUnit F ^ m : Fˣ)) : F) = (r ^ (-m)) ^ 2 := by
    rw [← GroundTheory.LocalField.distribHaarChar_eq_modulus, ← Measures.modulus_units, hmod]
  unfold mp
  rw [hbr, hS, NNReal.coe_pow, Complex.ofReal_pow]
  have h1 : (((r ^ (-m) : NNReal) : ℝ) : ℂ) ^ 2 = (((((r ^ (-m) : NNReal) : ℝ) ^ 2 : ℝ)) : ℂ) := by
    push_cast; rfl
  rw [h1]
  have h2 : ((1 : ℂ) / 2) = (((1 / 2 : ℝ)) : ℂ) := by push_cast; rfl
  rw [h2, ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq ht,
    NNReal.coe_zpow, Complex.ofReal_zpow]

end GlobalTheory.CompanionTheory.WS
