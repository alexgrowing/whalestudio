import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

def relabelBlocks {K K' : Type} {ι : K → Type} {ι' : K' → Type} (ε : K ≃ K')
    (h : ∀ k, ι k = ι' (ε k)) : (Σ k, ι k) ≃ (Σ k', ι' k') :=
  Equiv.sigmaCongr ε fun k => Equiv.cast (h k)

def NefOnFibresRelabel.Statement : Prop :=
  ∀ (K K' : Type) [Fintype K] [Fintype K'] (ι : K → Type) (ι' : K' → Type)
    [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))
    (Ω : Type) [Field Ω] (y : (Σ k', ι' k') → Ω) (a : K' → ℤ),
    NefOnFibres (mCoordIdeal (y ∘ relabelBlocks ε h)) (a ∘ ε) ↔ NefOnFibres (mCoordIdeal y) a

section Inhabitants

def optionToSum (K : Type) : Option K ≃ K ⊕ Unit where
  toFun
    | none => Sum.inr ()
    | some k => Sum.inl k
  invFun
    | Sum.inl k => some k
    | Sum.inr () => none
  left_inv := by rintro (_ | k) <;> rfl
  right_inv := by rintro (k | ⟨⟩) <;> rfl

theorem optionToSum_idx {K : Type} (ι : K → Type) (κ : Type) :
    ∀ o, (fun o : Option K => Option.elim o κ ι) o =
      Sum.elim ι (fun _ : Unit => κ) (optionToSum K o) := by
  rintro (_ | k) <;> rfl

example : relabelBlocks (optionToSum Unit) (optionToSum_idx (fun _ : Unit => Fin 2) (Fin 2))
    ⟨none, (1 : Fin 2)⟩ = ⟨Sum.inr (), (1 : Fin 2)⟩ := rfl

end Inhabitants

end GroundTheory.Heights₂.Heights
