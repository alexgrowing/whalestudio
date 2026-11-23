import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.IsRelCochain

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit

def IsRelExact {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) :
    {q : ℕ} → (Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) → Prop
  | 0, ω => ω = 0
  | _ + 1, ω => ∃ η, IsRelCochain Ξ (IsLevelFn U Ξ) η ∧ dCo (smLie Ξ) η = ω

def DeRhamInj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) →
    ∀ (Ξ : AlgRep E a) (q n : ℕ) (ω : Fin n → Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))),
      (∀ i, IsRelCochain Ξ (IsLevelFn U Ξ) (ω i) ∧ dCo (smLie Ξ) (ω i) = 0) →
      (∀ c : Fin n → ℂ, IsRelExact U Ξ (∑ i, c i • ω i) → c = 0) →
      (n : Cardinal) ≤ Module.rank ℂ (groupCohomology (Rep.of (levelRep ⊤ U (ratC Ξ))) q)

end UpperTheory.V.Lit
