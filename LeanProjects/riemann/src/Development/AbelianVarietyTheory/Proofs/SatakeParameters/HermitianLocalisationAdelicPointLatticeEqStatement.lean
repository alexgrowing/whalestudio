import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianLocalisationAdelicPointLatticeEq
import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.LocalToGlobal.Columns.RecLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapApply
open NumberField IsDedekindDomain Formalism.UG Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLocalisation_adelicPointLattice_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (Q : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)), Formalism.L2.Col.IsOver v Q → ∀ {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → ∀ (x x₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), bc (prV (E := E) v) x₁ = bc (prV (E := E) v) x → Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal (latAd x₁ Lb) = Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal (latAd x Lb) := by
  first | exact @GlobalTheory.LatAdLoc.loc_latAd_eq | exact GlobalTheory.LatAdLoc.loc_latAd_eq | (intros; apply GlobalTheory.LatAdLoc.loc_latAd_eq <;> assumption)
