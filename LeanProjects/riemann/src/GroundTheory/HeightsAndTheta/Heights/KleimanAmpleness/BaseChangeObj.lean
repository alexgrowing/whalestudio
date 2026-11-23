import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u u' w

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

def SubSystem.baseChange (O : Type u') [CommRing O] [Algebra O Ω] (Q : SubSystem S x Ω) : SubSystem O x Ω where
  sub I := Submodule.span (chartRing O x I) (Q.sub I : Set Ω)
  mono I₁ I₂ h z hz := by
    refine Submodule.span_induction
      (p := fun z _ => z ∈ Submodule.span (chartRing O x I₂) (Q.sub I₂ : Set Ω)) ?_ ?_ ?_ ?_ hz
    · intro z hz; exact Submodule.subset_span (Q.mono I₁ I₂ h z hz)
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; exact Submodule.smul_mem _ (chartIncl h a) hz

end

end GroundTheory.Heights₂.Heights.Kleiman
