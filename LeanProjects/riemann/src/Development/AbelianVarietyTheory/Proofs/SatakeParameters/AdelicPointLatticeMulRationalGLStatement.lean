import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointLatticeMulRationalGL
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicPointLattice_mul_rationalGL : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ} (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)), latAd (y * ratA F g) M = latAd y (mvL g M) := by
  first | exact @GlobalTheory.TwV.latAd_mul_ratA | exact GlobalTheory.TwV.latAd_mul_ratA | (intros; apply GlobalTheory.TwV.latAd_mul_ratA <;> assumption)
