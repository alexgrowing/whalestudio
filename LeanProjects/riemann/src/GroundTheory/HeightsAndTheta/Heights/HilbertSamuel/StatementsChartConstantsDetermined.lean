import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConstantsRegular
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry NumberField

def intsIn (F Ω : Type*) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] : Subalgebra ℤ Ω :=
  ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).toIntAlgHom.range

def ChartConstantsDetermined.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω),
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∀ w w' : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ,
      w.comp (Subalgebra.inclusion (le_sup_left : chartRingZ y c ≤ chartRingZ y c ⊔ intsIn F Ω)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_left : chartRingZ y c ≤ chartRingZ y c ⊔ intsIn F Ω)).toRingHom →
        w.comp (Subalgebra.inclusion (le_sup_right : intsIn F Ω ≤ chartRingZ y c ⊔ intsIn F Ω)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_right : intsIn F Ω ≤ chartRingZ y c ⊔ intsIn F Ω)).toRingHom

section Inhabitants

open ProjLine

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
