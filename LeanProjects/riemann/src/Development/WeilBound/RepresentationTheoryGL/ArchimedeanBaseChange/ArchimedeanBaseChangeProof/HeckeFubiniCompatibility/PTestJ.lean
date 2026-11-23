import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotIntegralZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PTestVeryCuspMulConst

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)

namespace PositivityTheory.Rg.BcB.CG

def Test2J : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  (fa : InfinitePlace E → G a → ℂ) (fb : InfinitePlace E → G b → ℂ) (ψ : Hf E a b → ℂ) (R r : ℝ)
  (U : Subgroup (Hf E a b)), 0 ≤ R →
  (∀ v, Continuous (fa v) ∧ VeryCusp (fa v) ∧ ∀ y, fa v y ≠ 0 → lg y.val ≤ R) →
  (∀ v, Continuous (fb v) ∧ VeryCusp (fb v) ∧ ∀ y, fb v y ≠ 0 → lg y.val ≤ R) →
  HasCompactSupport ψ → IsOpen (U : Set (Hf E a b)) → (∀ u ∈ U, ∀ h, ψ (u * h) = ψ h ∧ ψ (h * u) = ψ h) →
  (∀ h, ψ h ≠ 0 → logSize (finGL E a h.1) ≤ r ∧ logSize (finGL E b h.2) ≤ r) →
  (∀ d x h₂, ψ (gFin (PositivityTheory.Rg.Tf.Loc.twConj (thetaA E a) x (ratGL E a d)), h₂) ≠ 0 → IsRegD d) →
  (∀ d x h₁, ψ (h₁, gFin (PositivityTheory.Rg.Tf.Loc.twConj (thetaA E b) x (ratGL E b d))) ≠ 0 → IsRegD d) →
  PositivityTheory.Rg.BcB.D4.IsTest2J (fun g : H E a b => (∏ v, fa v (gInf v g.1)) * (∏ v, fb v (gInf v g.2)) * ψ (hFin g))
    (2 * Fintype.card (InfinitePlace E) * R + r)

theorem test2J : Test2J := fun E _ _ _ a b fa fb ψ R r U hR ha hb hψs hUo hψU hsz hr₁ hr₂ =>
  have h := pTest_main fa fb ψ R r U hR ha hb hψs hUo hψU hsz hr₁ hr₂
  { toIsTest2 := h.1, level := h.2 }

end PositivityTheory.Rg.BcB.CG
