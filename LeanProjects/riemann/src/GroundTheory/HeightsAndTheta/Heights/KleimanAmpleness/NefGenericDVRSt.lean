import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

noncomputable section

def NefGenericDVR.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (F : Type) [Field F] [Algebra O F]
    [IsFractionRing O F] (Ω : Type) [Field Ω] [Algebra O Ω] [Algebra F Ω] [IsScalarTower O F Ω]
    (N : ℕ) (x : Fin (N + 1) → Ω) (M : Kleiman.LineBundle O x),
    Kleiman.NefAbove M.toSubSystem ((IsLocalRing.maximalIdeal O).map (C : O →+* Kleiman.Poly O N)) →
    Kleiman.Nef (M.toSubSystem.extend F)

abbrev exO : Type := PowerSeries ℚ

abbrev exF : Type := FractionRing exO

abbrev exΩ : Type := RatFunc exF

theorem NefGenericDVR.hyps :
    Kleiman.NefAbove (Kleiman.twistBundle exO (Kleiman.lineX exF) 0).toSubSystem
      ((IsLocalRing.maximalIdeal exO).map (C : exO →+* Kleiman.Poly exO 1)) :=
  fun pp _ _ => by
    rw [show (Kleiman.twistBundle exO (Kleiman.lineX exF) 0).toSubSystem =
      Kleiman.twistSys exO (Kleiman.lineX exF) 0 from rfl, Kleiman.interNum_twistSys_zero]

example (h : NefGenericDVR.Statement) :=
  h exO exF exΩ 1 (Kleiman.lineX exF) (Kleiman.twistBundle exO (Kleiman.lineX exF) 0) NefGenericDVR.hyps

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
