import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsPerfectOfIsDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPairingPerfectOrthogonalOfKernelsZeroStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PoincareDeRhamDualityProof

theorem poincareDeRhamDuality_of_hodge (H : GlobalTheory.Published.AbelianHodgeDeRham) (D : GlobalTheory.Published.DualAbelianScheme) :
    GlobalTheory.Published.PoincareDeRhamDuality := by
  intro R _ A B _ _ g hA hB hg hg' P hP φ hφ
  exact GlobalTheory.T.deRham_pairing_perfect_and_hodge_filtration_isotropic H R A B g hA hB hg hg' P
    (GlobalTheory.Published.PoincareDeRhamDuality.Test.isPerfect_of_isDual D hA hP) φ hφ

end GlobalTheory.PoincareDeRhamDualityProof
