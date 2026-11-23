import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootDivisorsOfFrameBundle
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFramePullbackSections
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagCell GlobalTheory.FlagConnect GlobalTheory.CovTest GlobalTheory.FlagOverField
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_root_divisors_of_frame_bundle : ∀ (F : Type) [Field F] (Y : Var F) (ι : Type) [Fintype ι] (r : ι → ℕ) (E : ι → (Sp F).Modules) (e : ∀ a, Fin (r a) → Γ(E a, ⊤)) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback Y.str).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → (∀ a, IsFrame (e a)) → ∀ E' : Fr (ratOf Y) r r, (∀ y A', A' ∈ E'.S y ↔ AdFrame e fl y A') → ∃ gr : GlobalTheory.GoodMetric.Root r → Y.Dv, (∀ x, GlobalTheory.Cartier.toPic (gr x) = GlobalTheory.CechPic.cls ((fl x.1).root x.2) ((fl x.1).isLB_root x.2)) ∧ GlobalTheory.GoodMetric.IsGraded E' gr := by
  first | exact @GlobalTheory.FlagOverField.exists_graded | exact GlobalTheory.FlagOverField.exists_graded | (intros; apply GlobalTheory.FlagOverField.exists_graded <;> assumption)
