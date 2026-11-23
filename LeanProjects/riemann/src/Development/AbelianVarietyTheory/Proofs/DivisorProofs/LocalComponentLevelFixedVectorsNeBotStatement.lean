import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentLevelFixedVectorsNeBot
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localComponent_levelFixedVectors_ne_bot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → (∀ v, HasWeightAt π v.embedding (lam v)) → π ⊓ fixed (RF E n) (globLev S K') ≠ ⊥ → ∀ w ∈ S, ∀ σ : SmIrr (UL n w), IsCompU π w σ → fixed σ.ρ (K' w) ≠ ⊥ := by
  first | exact @GlobalTheory.BCT.LocFix.fixed_ne_bot | exact GlobalTheory.BCT.LocFix.fixed_ne_bot | (intros; apply GlobalTheory.BCT.LocFix.fixed_ne_bot <;> assumption)
