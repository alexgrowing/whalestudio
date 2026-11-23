import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFamilyFiniteDimSpan
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_family_finite_dim_span : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (T : Type) (Ψ : T → (κ → AF F) → ℂ), (∀ t, Ψ t ∈ schA F κ) →
    (∀ l ∈ (adeleClass F).adm κ, ∃ C : ℝ, ∀ t, ‖l (Ψ t)‖ ≤ C) →
    ∃ W : Submodule ℂ ((κ → Af F) → ℂ), FiniteDimensional ℂ W ∧
      ∀ t (y : κ → Ainf F), (fun z : κ → Af F => Ψ t (fun i => GlobalTheory.HeisSchA.mk (y i) (z i))) ∈ W := by
  first | exact @GlobalTheory.SliceFinDim.slices_of_bounded | exact GlobalTheory.SliceFinDim.slices_of_bounded | (intros; apply GlobalTheory.SliceFinDim.slices_of_bounded <;> assumption)
