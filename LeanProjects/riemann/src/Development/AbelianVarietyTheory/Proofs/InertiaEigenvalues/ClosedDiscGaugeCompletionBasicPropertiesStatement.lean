import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionBasicProperties
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedDiscGaugeCompletion_basic_properties : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (u : A) (ρ : ℝ≥0), IsUltrametricDist (Disc l u ρ) ∧ (∀ y : Disc l u ρ, ‖((l : ℕ) : Disc l u ρ) * y‖ = ‖y‖ / l) ∧ (∀ (N : Type) [NormedAddCommGroup N], (∀ z : N, l • z = 0 → z = 0) → ∀ F G : Disc l u ρ →+ N, Continuous F → Continuous G → (∀ a, F (toDisc l u ρ a) = G (toDisc l u ρ a)) → F = G) ∧ ∀ (A' A'' : Type) [CommRing A'] [CommRing A''] (u' : A') (u'' : A'') (ρ' ρ'' : ℝ≥0) (f : A →+* A') (f' : A' →+* A'') (F : Disc l u ρ →+* Disc l u' ρ') (F' : Disc l u' ρ' →+* Disc l u'' ρ''), IsDiscMap f F → IsDiscMap f' F' → IsDiscMap (f'.comp f) (F'.comp F) := by
  first | exact @GlobalTheory.BSP.DiscBasic.disc_basic | exact GlobalTheory.BSP.DiscBasic.disc_basic | (intros; apply GlobalTheory.BSP.DiscBasic.disc_basic <;> assumption)
