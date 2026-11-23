import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianRapidDecay

noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct

namespace GlobalTheory.AdeleBoundedCompact

theorem exists_compact_of_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (τ : ∀ w : NumberField.InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (C : Set (TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E)), IsCompact C → ∀ R : ℝ, ∃ K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E), IsCompact K ∧ ∀ z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E) z ∈ C → (∀ w, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (τ w) z‖ ≤ R) → z ∈ K := by
  intro F E _ _ _ _ _ σ h τ C hC R
  let θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ) := fun w =>
    (GlobalTheory.AdelicU.infEmb (τ w)).comp
      (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)).toRingHom
  have hθ : ∀ w, Formalism.MainNotions.StandardLattice.IsInfEmb (τ w).1 (θ w) := fun w => by
    refine ⟨fun x => ?_, ?_⟩
    · show GlobalTheory.AdelicU.infEmb (τ w) (GlobalTheory.AutFunCompare.evW w 1 ⊗ₜ[F] x) = _
      rw [GlobalTheory.AdelicU.infEmb_tmul, map_one, map_one, one_mul]
    · have e : (fun a : Ainf F => θ w (a ⊗ₜ[F] (1 : E))) =
          fun a => InfinitePlace.Completion.extensionEmbedding w (a w) := by
        funext a
        show GlobalTheory.AdelicU.infEmb (τ w) (GlobalTheory.AutFunCompare.evW w a ⊗ₜ[F] (1 : E)) = _
        rw [GlobalTheory.AdelicU.infEmb_tmul, map_one, mul_one]
        rfl
      rw [e]
      exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
  have hτ : GlobalTheory.Mem.Vol.IsCMFam (fun w => (τ w).1) :=
    GlobalTheory.GaussDecay.isCMFam_of_over σ h _ fun w a => RingHom.congr_fun (τ w).2 a
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.Mem.VolExists.exists_compact_adele h hτ hθ R C hC
  refine ⟨K, hK, fun z hz hR => hKe z hz fun w => ?_⟩
  have e : ∀ y : AE F E, θ w (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) y) = piInf (τ w) y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  rw [e z]
  exact hR w

end GlobalTheory.AdeleBoundedCompact
