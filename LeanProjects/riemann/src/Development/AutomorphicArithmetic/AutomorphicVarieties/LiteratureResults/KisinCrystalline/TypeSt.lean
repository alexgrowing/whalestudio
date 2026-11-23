import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KisinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TypeDeformAlg

noncomputable section

namespace UpperTheory.V.Lit

open Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Loc TensorProduct GlobalTheory.Pst

variable {l : ℕ} [Fact l.Prime] {B V : Type} [CommRing B] [Algebra ℚ_[l] B] [AddCommGroup V] [Module B V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] B V] (K : FinExt l) (ρ : Representation B ↥(GK K) V)

def TypeSt (n : ℕ) (t : ↥(GK K) → B) : Prop :=
  ∃ x : Fin n → V ⊗[ℚ_[l]] Bst (PP l), (∀ a, x a ∈ Dpst (PP l) (resCoef ℚ_[l] ρ)) ∧
    (∀ y ∈ Dpst (PP l) (resCoef ℚ_[l] ρ), ∃! c : Fin n → B ⊗[ℚ_[l]] ↥(MaximalUnramifiedExtension l),
      y = ∑ a, Thick.sm V (Bst (PP l)) (c a) (x a)) ∧
    ∀ γ : ↥(GK K), (γ : GQ l) ∈ Iq l → ∀ M : Matrix (Fin n) (Fin n) (B ⊗[ℚ_[l]] ↥(MaximalUnramifiedExtension l)),
      (∀ b, stRep (PP l) (resCoef ℚ_[l] ρ) γ (x b) = ∑ a, Thick.sm V (Bst (PP l)) (M a b) (x a)) →
      M.trace = t γ ⊗ₜ[ℚ_[l]] 1

end UpperTheory.V.Lit
