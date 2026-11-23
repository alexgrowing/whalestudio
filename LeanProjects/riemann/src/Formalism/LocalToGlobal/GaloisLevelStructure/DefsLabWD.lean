import Formalism.LocalToGlobal.GaloisLevelStructure.DefsGal
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLab
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.GaloisValuations.Global

noncomputable section

open NumberField IsDedekindDomain Polynomial ReciprocityTheory.Gal

namespace Formalism.L2.NG

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {p n : ℕ} [Fact p.Prime]
  {v : HeightOneSpectrum (𝓞 F)}

def WildAt (A : ValuationSubring Ω) : Set (Ω ≃ₐ[F] Ω) :=
  {σ | σ ∈ Ine (F := F) A ∧ ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}

end Formalism.L2.NG
