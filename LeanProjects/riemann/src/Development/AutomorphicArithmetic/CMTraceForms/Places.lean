import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule

set_option autoImplicit false

noncomputable section

namespace UpperTheory.Depth

open NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def SplitAt (d p : ℕ) : Prop := p = 2 ∨ jacobiSym (-(d : ℤ)) p = 1

def SplitPlaces (p : ℕ) [Fact p.Prime] (H : Host E) (f : ℕ) (vd : ℝ) : Prop :=
  letI := H.starRing
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C],
    v.Integers O → ∀ [Fact (¬ IsUnit (p : O))] [Algebra ℤ_[p] O] (τO : (E →+* ℂ) → (𝓞 E →+* O)),
    Function.Injective τO → (∀ τ τ', τ (H.rt : E) = τ' (H.rt : E) ↔ τO τ H.rt = τO τ' H.rt) →
    ∃ (s : ℕ) (w : Fin s → Place p (𝓞 E)) (vdi : Fin s → ℝ),
      ∑ i, (w i).n = f ∧ ∑ i, ((w i).n : ℝ) * vdi i = (f : ℝ) * vd ∧
      (∀ i σ, σ ∈ Emb (O := O) (w i).e → ∃ τ, InPsi H τ ∧ σ = τO τ) ∧
      (∀ τ, InPsi H τ → ∃! i, τO τ ∈ Emb (O := O) (w i).e) ∧
      (∀ i σ, σ ∈ Emb (O := O) (w i).bar → ∃ τ, ¬ InPsi H τ ∧ σ = τO τ) ∧
      ∀ i, ∃ t : Fin (w i).n ≃ Emb (O := O) (w i).e, HasVd p v (w i) t (vdi i)

end UpperTheory.Depth

end
