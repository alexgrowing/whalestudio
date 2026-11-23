import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetThreePointsEqExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditiveCharacterEquivariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSmoothness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerWellDefined
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecSet
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.SmallSec

namespace GlobalTheory.CompanionTheory.SmallSec

theorem modulus_eq_one_of_sub_one_mem_valBall_pos (F : Type) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (hn : 1 ≤ n) (a : Fˣ)
    (ha : (a : F) - 1 ∈ valBall F (n : ℤ)) : modulus (a : F) = 1 := by
  have hd : (a : F) - 1 ∈ valBall F (ord (1 : F) + 1) := by
    rw [ord_one, zero_add]
    exact valBall_antitone (by exact_mod_cast hn) ha
  have h := ord_add_eq (one_ne_zero : (1 : F) ≠ 0) hd
  rw [add_sub_cancel, ord_one] at h
  exact GroundTheory.LocalField.modulus_eq_one_iff.2 h

end GlobalTheory.CompanionTheory.SmallSec
