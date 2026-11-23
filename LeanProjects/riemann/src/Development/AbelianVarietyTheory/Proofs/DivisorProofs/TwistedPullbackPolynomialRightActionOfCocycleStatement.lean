import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPullbackPolynomialRightActionOfCocycle
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemDomOfIsom
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPullbackPolynomial_rightAction_of_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (a : U → C → ℂˣ), (∀ (g h : U) (c : C), a (h * g) c = a g c * a h (g • c)) → tw M (fun c => (a 1 c : ℂ)) 1 = AlgHom.id ℂ _ ∧ ∀ u v : U, (tw M (fun c => (a v c : ℂ)) v).comp (tw M (fun c => (a u c : ℂ)) u) = tw M (fun c => (a (u * v) c : ℂ)) (u * v) := by
  first | exact @GlobalTheory.CuspEmb.tw_law | exact GlobalTheory.CuspEmb.tw_law | (intros; apply GlobalTheory.CuspEmb.tw_law <;> assumption)
