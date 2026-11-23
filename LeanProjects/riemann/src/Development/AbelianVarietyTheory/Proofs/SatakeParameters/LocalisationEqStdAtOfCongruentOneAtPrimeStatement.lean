import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localisation_eq_stdAt_of_congruentOne_atPrime : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ), 1 ≤ d → ∀ (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (R : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)), M.FG → Submodule.span E (M : Set (Fin N → E)) = ⊤ → CongAt (F := F) P d (y⁻¹ * ratA F R) → Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (latAd y M) = mvL R (stdAt E N P) → Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M = stdAt E N P := by
  first | exact @GlobalTheory.CongStdLoc.localization_eq_stdAt_of_congAt | exact GlobalTheory.CongStdLoc.localization_eq_stdAt_of_congAt | (intros; apply GlobalTheory.CongStdLoc.localization_eq_stdAt_of_congAt <;> assumption)
