import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameBaseChangeFieldPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFramePullbackSections
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagCell GlobalTheory.FlagConnect GlobalTheory.CovTest GlobalTheory.FlagOverField
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_frame_base_change_field_point : ∀ (F : Type) [Field F] (Y : Var F) (ι : Type) [Fintype ι] (r : ι → ℕ) (E : ι → (Sp F).Modules) (e : ∀ a, Fin (r a) → Γ(E a, ⊤)) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback Y.str).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → (∀ a, IsFrame (e a)) → ∀ (L : Type) [Field L] (p : Sp L ⟶ Y.X) (x : Sp L ⟶ Sp F) (w : p ≫ Y.str = x) (h : Mat r L) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback x).obj (E a)) (r a)), (∀ a, Spans (fl' a) ⊤ (pullCol x (e a) le_top ((h a).transpose.map (Scheme.ΓSpecIso (.of L)).inv.hom))) → ∀ A' : Mat r Y.Fn, AdFrame e fl (p (IsLocalRing.closedPoint L)) A' → (Carries Y.str E r fl p x w fl' ↔ Par r ⊤ (h * (A'.map ((ratOf Y).val p))⁻¹)) := by
  first | exact @GlobalTheory.FlagOverField.AdCarr.carries_iff_par | exact GlobalTheory.FlagOverField.AdCarr.carries_iff_par | (intros; apply GlobalTheory.FlagOverField.AdCarr.carries_iff_par <;> assumption)
