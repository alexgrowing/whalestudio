import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top

namespace GlobalTheory.Fc.PeriodEntriesOverColumns

open GlobalTheory.Fc

def ReferenceChainEvaluationAdmissible (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (Fm.D x i) u

def ReferenceChainEvaluationAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => ReferenceChainEvaluationAdmissible 𝒜

def H_aPtTw (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPointIntegral (Fm.D x i) (Fm.ex x hx i).tw

def TwistedPointAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_aPtTw 𝒜

def H_aPer0 (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl (Fm.D x i)

def PeriodAtZeroAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_aPer0 𝒜

def H_aPerTw (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw

def TwistedPeriodAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_aPerTw 𝒜

def H_tie (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => Formalism.MainNotions.RealPlaceSecondLayerConditions Fm

def Row_tie {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_tie 𝒜

structure All (𝒜 : FamClass) : Prop where
  aPt0 : ReferenceChainEvaluationAdmissible 𝒜
  aPtTw : H_aPtTw 𝒜
  aPer0 : H_aPer0 𝒜
  aPerTw : H_aPerTw 𝒜
  tie : H_tie 𝒜

theorem row_all {Bd : BdT} {Q : V4.Slot} {Lk : LkT Bd}
    (aPt0 : ReferenceChainEvaluationAtBundlePoints Q Lk) (aPtTw : TwistedPointAtBundlePoints Q Lk) (aPer0 : PeriodAtZeroAtBundlePoints Q Lk) (aPerTw : TwistedPeriodAtBundlePoints Q Lk) (tie : Row_tie Q Lk) :
    Row Q Lk fun 𝒜 _ => All 𝒜 :=
  Row.imp (Row.and aPt0 (Row.and aPtTw (Row.and aPer0 (Row.and aPerTw tie))))
    fun _ _ _ ⟨a0, a1, a2, a3, a4⟩ => ⟨a0, a1, a2, a3, a4⟩

example (𝒜 : FamClass) : H_aPerTw 𝒜 ↔ EvC (fun D O => Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible D O.X O.ex.tw) 𝒜 := Iff.rfl

end GlobalTheory.Fc.PeriodEntriesOverColumns

end
