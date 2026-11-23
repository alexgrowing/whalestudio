import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameParahoricTransition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFramePullbackSections
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagCell GlobalTheory.FlagConnect GlobalTheory.CovTest GlobalTheory.FlagOverField
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_frame_parahoric_transition : ∀ (F : Type) [Field F] (Y : Var F) (ι : Type) [Fintype ι] (r : ι → ℕ) (E : ι → (Sp F).Modules) (e : ∀ a, Fin (r a) → Γ(E a, ⊤)) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback Y.str).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → (∀ a, IsFrame (e a)) → ∀ (y : Y.X) (A : Mat r Y.Fn), AdFrame e fl y A → Par 0 ((ratOf Y).O y).toSubring A ∧ ∀ A' : Mat r Y.Fn, AdFrame e fl y A' → Par r ((ratOf Y).O y).toSubring (A' * A⁻¹) := by
  first | exact @GlobalTheory.FlagOverField.adFrame_par | exact GlobalTheory.FlagOverField.adFrame_par | (intros; apply GlobalTheory.FlagOverField.adFrame_par <;> assumption)
