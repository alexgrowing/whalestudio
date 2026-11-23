import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedLatticeOfLinearAutImageEqMatrixImage
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.MqRowSGUnif
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedLattice_of_linearAutImage_eq_matrixImage : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) (N : Submodule (𝓞 X.E) (Sp X.E n)), s.lat (Formalism.HermitianLatticesTheory.gmap g N) = Formalism.MainNotions.G.KAat.mvL (seamGL s g) (s.lat N) := by
  first | exact @GlobalTheory.RatLat.lat_gmap | exact GlobalTheory.RatLat.lat_gmap | (intros; apply GlobalTheory.RatLat.lat_gmap <;> assumption)
