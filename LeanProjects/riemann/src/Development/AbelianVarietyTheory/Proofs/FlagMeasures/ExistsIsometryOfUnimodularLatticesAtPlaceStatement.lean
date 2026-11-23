import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryOfUnimodularLatticesAtPlace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_of_unimodular_lattices_at_place : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (L L' : Submodule (𝓞 K) V), Submodule.IsLattice K L → Submodule.IsLattice K L' → ∀ P : Ideal (𝓞 K), P.IsMaximal → IsUnimodularAt h P L → IsUnimodularAt h P L' → ∃ g ∈ isom h, gmap g (loc (K := K) P L) = loc (K := K) P L' := by
  first | exact @GlobalTheory.Mass.UnimodLoc.exists_isom_of_isUnimodularAt | exact GlobalTheory.Mass.UnimodLoc.exists_isom_of_isUnimodularAt | (intros; apply GlobalTheory.Mass.UnimodLoc.exists_isom_of_isUnimodularAt <;> assumption)
