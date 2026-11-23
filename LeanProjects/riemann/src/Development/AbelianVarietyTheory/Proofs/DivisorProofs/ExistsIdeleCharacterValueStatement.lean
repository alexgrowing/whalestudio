import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleCharacterValue
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idele_character_value : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, EmbOver E w) (w₀ : InfinitePlace F) (ξ : E), ξ ≠ 0 → ∃ t : (AE F E)ˣ, ∀ (χ : Chr F E) (m : InfinitePlace F → ℤ), HasExp emb χ m → (χ t : ℂ) = ((emb w₀).1 ξ / (‖(emb w₀).1 ξ‖ : ℂ)) ^ m w₀ := by
  first | exact @GlobalTheory.IdeleAtPlace.exists_idele_char_eq | exact GlobalTheory.IdeleAtPlace.exists_idele_char_eq | (intros; apply GlobalTheory.IdeleAtPlace.exists_idele_char_eq <;> assumption)
