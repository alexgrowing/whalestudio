import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.AdelicU

theorem eventually_vecLoc_mem_latLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) (y : Fin n → Af F ⊗[F] E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, vecLoc v y ∈ latLoc F L v := by
  have := isLattice_stdLattice (E := E) (n := n)
  filter_upwards [eventually_latLoc_eq F L (stdLattice E n),
    Filter.eventually_all.2 fun i => eventually_map_evalV_mem_intLoc (y i)] with v h h1
  rw [h, mem_latLoc_stdLattice]
  exact h1

theorem indicator_latHat_eq_finprod :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
      (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ X : Fin 1 → Fin n → Af F ⊗[F] E,
      {X : Fin 1 → Fin n → Af F ⊗[F] E | X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))}.indicator
        (1 : (Fin 1 → Fin n → Af F ⊗[F] E) → ℂ) X =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator
          (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ) (projV v X) := by
  intro F E _ _ _ _ _ n L hL X
  have key : ∀ v : HeightOneSpectrum (𝓞 F), vecLoc v (X 0) ∈ latLoc F L v →
      {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator
          (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ) (projV v X) = 1 := fun v hv =>
    Set.indicator_of_mem (s := {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}) hv _
  by_cases h : X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))
  · rw [Set.indicator_of_mem
      (s := {X : Fin 1 → Fin n → Af F ⊗[F] E | X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))}) h,
      finprod_congr fun v => key v ((mem_latHat_iff hL.fg _).1 h v), finprod_one]
    rfl
  · rw [Set.indicator_of_notMem
      (s := {X : Fin 1 → Fin n → Af F ⊗[F] E | X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))}) h]
    rw [mem_latHat_iff hL.fg, not_forall] at h
    obtain ⟨v, hv⟩ := h
    refine (finprod_eq_zero _ v ?_ ?_).symm
    · exact Set.indicator_of_notMem
        (s := {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}) hv _
    · exact Set.Finite.subset (Filter.eventually_cofinite.1 (eventually_vecLoc_mem_latLoc L hL (X 0)))
        fun u hu hu' => hu (key u hu')

end GlobalTheory.AdelicU
