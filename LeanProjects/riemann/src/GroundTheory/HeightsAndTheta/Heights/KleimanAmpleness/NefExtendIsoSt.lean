import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

def NefExtendIso.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (F : Type) [Field F] [Algebra S F] (Ω : Type) [Field Ω] [Algebra S Ω]
    [Algebra F Ω] [IsScalarTower S F Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (Q : Kleiman.SubSystem S x Ω),
    Function.Bijective (algebraMap S F) → Kleiman.Nef Q → Kleiman.Nef (Q.extend F)

theorem NefExtendIso.hyps :
    Function.Bijective (algebraMap ℚ ℚ) ∧
      Kleiman.Nef (Kleiman.twistSys ℚ (Kleiman.lineX ℚ) 0) :=
  ⟨Function.bijective_id, Kleiman.nef_twistSys_zero⟩

example (h : NefExtendIso.Statement) :=
  h ℚ ℚ (RatFunc ℚ) 1 (Kleiman.lineX ℚ) _ NefExtendIso.hyps.1 NefExtendIso.hyps.2

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
