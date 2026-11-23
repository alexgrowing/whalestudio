import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PsType

def TypesChars : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (n : ℕ) (χ : Fin n → Weil h →* ℂˣ) (hχ : ∀ i, IsSmooth (χ i)),
      ∃ (d : ℕ) (ξ : Representation ℂ ↥(GlobalTheory.LFun.KGL w n) (Fin d → ℂ)), GlobalTheory.PRep.IsSmooth ξ ∧
        ∀ π : SmIrr (GL (Fin n) (w.adicCompletion E)),
          (∃ f : (Fin d → ℂ) →ₗ[ℂ] π.V, f ≠ 0 ∧ ∀ k v, f (ξ k v) = π.ρ k (f v)) ↔
            ((rc (IrrGL.of π.ρ π.smooth π.irred)).mono0 ∧ ∀ s : ↥(Ine (F := E) A),
              (rc (IrrGL.of π.ρ π.smooth π.irred)).charPol (ineIncl h s) =
                (WD.mk (WDRep.ofChars h χ hχ)).charPol (ineIncl h s))

end GlobalTheory.PsType
