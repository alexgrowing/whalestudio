import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLevelFixedVectorsDefiniteUnitaryEqProd
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_levelFixedVectors_definiteUnitary_eq_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Set (Pl E), IsSection S → ∀ lam : InfinitePlace E → DomWeight n, (∀ v, HasWeightAt π v.embedding (lam v)) → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ σ : ∀ w : Pl E, SmIrr (UL n w), (∀ w, IsCompU π w (σ w)) → (Module.finrank ℂ ↥(π ⊓ fixed (RF E n) (globLev S K')) : ℂ) = dimW lam * ∏ᶠ w ∈ S, (Module.finrank ℂ (fixed (σ w).ρ (K' w)) : ℂ) := by
  first | exact @GlobalTheory.BCT.DimFac.finrank_inf_fixed_globLev | exact GlobalTheory.BCT.DimFac.finrank_inf_fixed_globLev | (intros; apply GlobalTheory.BCT.DimFac.finrank_inf_fixed_globLev <;> assumption)
