import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeneralizedEigenPartProjectorMemHeckeAlgebra
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generalizedEigenPartProjector_mem_heckeAlgebra : ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V] (S : Set (Module.End K V)), (∀ a ∈ S, ∀ b ∈ S, Commute a b) → (∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤) → (∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range) → ∀ (L : Submodule O V), L.FG → Submodule.span K (L : Set V) = ⊤ → (∀ a ∈ S, ∀ x ∈ L, a x ∈ L) → ∀ 𝔪 : Ideal (Algebra.adjoin O S), ∃ t ∈ Algebra.adjoin O S, (∀ x ∈ NCov.part (Algebra.adjoin O S) 𝔪, t x = x) ∧ ∀ x ∈ NCov.off (Algebra.adjoin O S) 𝔪, t x = 0 := by
  first | exact @GlobalTheory.part_projector_mem_adjoin | exact GlobalTheory.part_projector_mem_adjoin | (intros; apply GlobalTheory.part_projector_mem_adjoin <;> assumption)
