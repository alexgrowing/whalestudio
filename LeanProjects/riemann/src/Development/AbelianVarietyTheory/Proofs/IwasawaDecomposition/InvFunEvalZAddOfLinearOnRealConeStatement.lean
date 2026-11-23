import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvFunEvalZAddOfLinearOnRealCone
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invFun_evalZ_add_of_linearOn_realCone : ∀ (O : Type) [CommRing O] (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), ψ.LinearOn v → ∀ β x : LinearMap.BilinForm ℤ X, InRCone v β → InRCone v x → ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x := by
  first | exact @GlobalTheory.PolFan.Mark.evalZ_add_of_linearOn_inRCone | exact GlobalTheory.PolFan.Mark.evalZ_add_of_linearOn_inRCone | (intros; apply GlobalTheory.PolFan.Mark.evalZ_add_of_linearOn_inRCone <;> assumption)
