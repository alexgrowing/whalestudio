import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemBtOrderIffBtSet
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_btOrder_iff_btSet : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → R), f ∈ Γ.btOrder U ↔ f ∈ Γ.btSet U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.mem_btOrder_iff_mem_btSet | exact GlobalTheory.CompanionTheory.Ar.BT.mem_btOrder_iff_mem_btSet | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.mem_btOrder_iff_mem_btSet <;> assumption)
