import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureChangeFramedGeometricPointUnique
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
open CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LevPull
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelStructureChange_framedGeometricPoint_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La), IsLift lift → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y y' : FrPt Xo c k) (γ γ' : Gam Dw l), levR (lift γ, LinearMap.id) y y' → levR (lift γ', LinearMap.id) y y' → γ = γ' := by
  first | exact @GlobalTheory.LevelFree.move_unique | exact GlobalTheory.LevelFree.move_unique | (intros; apply GlobalTheory.LevelFree.move_unique <;> assumption)
