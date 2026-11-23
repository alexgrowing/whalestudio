import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedNormCompactPreimage
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_norm_compact_preimage : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (τ : ∀ w : NumberField.InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (C : Set (TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E)), IsCompact C → ∀ R : ℝ, ∃ K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E), IsCompact K ∧ ∀ z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E) z ∈ C → (∀ w, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (τ w) z‖ ≤ R) → z ∈ K := by
  first | exact @GlobalTheory.AdeleBoundedCompact.exists_compact_of_bounded | exact GlobalTheory.AdeleBoundedCompact.exists_compact_of_bounded | (intros; apply GlobalTheory.AdeleBoundedCompact.exists_compact_of_bounded <;> assumption)
