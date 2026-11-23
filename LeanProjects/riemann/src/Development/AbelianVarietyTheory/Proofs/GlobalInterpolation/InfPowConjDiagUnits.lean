import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal

namespace GlobalTheory.HeckeGal

theorem infPow_infDiag {E : Type} [Field E] [NumberField E] (n : (E →+* ℂ) → ℤ) (k : Eˣ) :
    infPow n (infDiag k) = infPow n (diagUnits E k) := by
  have h : ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E).1 = ((diagUnits E k : Ideles E) : AdeleRing (𝓞 E) E).1 := by
    rw [infDiag_eq]
    rfl
  simp only [infPow, h]

end GlobalTheory.HeckeGal

end
