import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizationUnimodularCompanionEq
import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
open NumberField Formalism.BasicNotions Formalism.L2.PairingIndexBounds.F

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_unimodularCompanion_eq : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Q : Ideal (𝓞 E)) (Λ Λ₁ : Submodule (𝓞 E) (Fin N → E)), Λ.FG → Λ₁.FG → Formalism.HermitianLatticesTheory.loc (K := E) Q Λ = Formalism.HermitianLatticesTheory.loc (K := E) Q Λ₁ → Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ) = Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ₁) := by
  first | exact @GlobalTheory.loc_compan_eq | exact GlobalTheory.loc_compan_eq | (intros; apply GlobalTheory.loc_compan_eq <;> assumption)
