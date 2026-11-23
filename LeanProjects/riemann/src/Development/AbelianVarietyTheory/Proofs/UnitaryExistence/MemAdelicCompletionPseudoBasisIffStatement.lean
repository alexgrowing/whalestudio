import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemAdelicCompletionPseudoBasisIff
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_adelicCompletion_pseudoBasis_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (e : Module.Basis (Fin n) E (Fin n → E)) (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E), (∀ v, v ∈ L ↔ ∀ a, e.repr v a ∈ cI a) → ∀ z : Fin n → RA F E, (∑ a, z a • fv F (e a)) ∈ (hat F (L : Set (Fin n → E))) ↔ ∀ a, z a ∈ hat1 F (cI a : Set E) := by
  first | exact @GlobalTheory.AdLat.mem_hat_pseudoBasis_iff | exact GlobalTheory.AdLat.mem_hat_pseudoBasis_iff | (intros; apply GlobalTheory.AdLat.mem_hat_pseudoBasis_iff <;> assumption)
