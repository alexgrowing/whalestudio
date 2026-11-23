import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalAdaptedFrameMatrix
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFramePullbackSections
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagCell GlobalTheory.FlagConnect GlobalTheory.CovTest GlobalTheory.FlagOverField
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_adapted_frame_matrix : ∀ (F : Type) [Field F] (Y : Var F) (ι : Type) [Fintype ι] (r : ι → ℕ) (E : ι → (Sp F).Modules) (e : ∀ a, Fin (r a) → Γ(E a, ⊤)) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback Y.str).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → (∀ a, IsFrame (e a)) → ∀ y : Y.X, ∃ (U : Y.X.Opens) (A : Mat r Y.Fn), y ∈ U ∧ ∀ z ∈ U, AdFrame e fl z A := by
  first | exact @GlobalTheory.FlagOverField.exists_adFrame_near | exact GlobalTheory.FlagOverField.exists_adFrame_near | (intros; apply GlobalTheory.FlagOverField.exists_adFrame_near <;> assumption)
