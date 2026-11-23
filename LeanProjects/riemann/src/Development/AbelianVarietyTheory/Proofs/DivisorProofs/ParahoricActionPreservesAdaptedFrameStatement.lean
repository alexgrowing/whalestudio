import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParahoricActionPreservesAdaptedFrame
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFramePullbackSections
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagCell GlobalTheory.FlagConnect GlobalTheory.CovTest GlobalTheory.FlagOverField
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoric_action_preserves_adapted_frame : ∀ (F : Type) [Field F] (Y : Var F) (ι : Type) [Fintype ι] (r : ι → ℕ) (E : ι → (Sp F).Modules) (e : ∀ a, Fin (r a) → Γ(E a, ⊤)) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback Y.str).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → (∀ a, IsFrame (e a)) → ∀ (y : Y.X) (A g : Mat r Y.Fn), AdFrame e fl y A → Par r ((ratOf Y).O y).toSubring g → AdFrame e fl y (g * A) := by
  first | exact @GlobalTheory.FlagOverField.adFrame_par_mul | exact GlobalTheory.FlagOverField.adFrame_par_mul | (intros; apply GlobalTheory.FlagOverField.adFrame_par_mul <;> assumption)
