import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseChangePointsCompat
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_points_compat : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ t, (Γ'.pt t).left ≫ F = Spec.map (CommRingCat.ofHom κ) ≫ (Γ.pt t).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.genericPoint_baseChange | exact GlobalTheory.CompanionTheory.Ar.BT.genericPoint_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.genericPoint_baseChange <;> assumption)
