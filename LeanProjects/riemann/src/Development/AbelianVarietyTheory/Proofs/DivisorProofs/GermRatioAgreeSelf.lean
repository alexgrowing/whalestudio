import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.Mum

variable {X Z : Scheme.{0}} {k : ℕ}

def GermRatioAgree {L : LB X} (v v' : Z ⟶ X) (s₀ : H0 L k) (i i'' : Fin 1 → L.ι) (z : Z) : Prop :=
  v z ∈ secChart L i ∧ v' z ∈ secChart L i'' ∧
    IsUnit (secGerm v z s₀ i) ∧ IsUnit (secGerm v' z s₀ i'') ∧
    ∀ s₁ : H0 L k, secGerm v z s₁ i * secGerm v' z s₀ i'' = secGerm v z s₀ i * secGerm v' z s₁ i''

end GlobalTheory.Mum
