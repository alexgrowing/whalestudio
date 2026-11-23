import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfFixedVectorsAdelicLevelNeBotOfLocalLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inf_fixedVectors_adelicLevel_ne_bot_of_localLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → HasLevel S π K' → π ⊓ fixed (RF E n) (globLev S K') ≠ ⊥ := by
  first | exact @GlobalTheory.FixLev.inf_fixed_globLev_ne_bot | exact GlobalTheory.FixLev.inf_fixed_globLev_ne_bot | (intros; apply GlobalTheory.FixLev.inf_fixed_globLev_ne_bot <;> assumption)
