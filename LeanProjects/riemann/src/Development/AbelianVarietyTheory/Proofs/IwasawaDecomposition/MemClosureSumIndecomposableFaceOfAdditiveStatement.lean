import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemClosureSumIndecomposableFaceOfAdditive
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_sum_indecomposable_face_of_additive : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ lab : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X), (∀ x y, InFace bar ψ lab β x → InFace bar ψ lab β y → InFace bar ψ lab β (x + y) ∧ ψ.evalZ (x + y) = ψ.evalZ x + ψ.evalZ y) → (∀ x, InFace bar ψ lab β x → ∃ n : ℤ, ψ.evalZ x = n) → (∀ x, InFace bar ψ lab β x → x ≠ 0 → 0 < ψ.evalZ x) → ∀ x, InFace bar ψ lab β x → x ∈ AddSubmonoid.closure {y | IsIndec bar ψ lab β y} := by
  first | exact @GlobalTheory.PolFan.Mark.mem_closure_isIndec | exact GlobalTheory.PolFan.Mark.mem_closure_isIndec | (intros; apply GlobalTheory.PolFan.Mark.mem_closure_isIndec <;> assumption)
