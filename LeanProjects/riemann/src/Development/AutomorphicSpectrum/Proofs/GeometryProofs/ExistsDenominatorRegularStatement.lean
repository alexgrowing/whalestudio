import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorRegular
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denominator_regular : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (f : T → FractionRing R) (g : Γ.G.left), ∃ d : R, d ≠ 0 ∧ Γ.RegularAt (fun t => algebraMap R _ d * f t) g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.RegDenom.exists_denom_regularAt | exact GlobalTheory.CompanionTheory.Ar.BT.RegDenom.exists_denom_regularAt | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.RegDenom.exists_denom_regularAt <;> assumption)
