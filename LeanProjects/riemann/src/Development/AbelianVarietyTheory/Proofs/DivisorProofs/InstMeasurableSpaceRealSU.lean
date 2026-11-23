import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames

noncomputable section
namespace GlobalTheory.SUVol
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

instance instMeasurableSpaceRealSU (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) :
    MeasurableSpace (realSU Ψ G) := borel _
instance instBorelSpaceRealSU (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) :
    BorelSpace (realSU Ψ G) := ⟨rfl⟩
end GlobalTheory.SUVol
end
