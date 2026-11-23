import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointLatticeFgOfFull
import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
open NumberField IsDedekindDomain Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicPointLattice_fg_of_full : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → ∀ (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), (latAd x Lb).FG := by
  first | exact @GlobalTheory.LatAdFG.latAd_fg_of_full | exact GlobalTheory.LatAdFG.latAd_fg_of_full | (intros; apply GlobalTheory.LatAdFG.latAd_fg_of_full <;> assumption)
