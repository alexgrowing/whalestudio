import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WcEqZero
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

noncomputable section
namespace GlobalTheory.CompanionTheory.NormLocal
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
theorem isOpenEmbedding_units_val' [IsTopologicalDivisionRing F] [T1Space F] :
    Topology.IsOpenEmbedding (Units.val : Fˣ → F) := by
  refine ⟨Units.isEmbedding_val₀, ?_⟩
  have : Set.range (Units.val : Fˣ → F) = {0}ᶜ := by
    ext a
    constructor
    · rintro ⟨u, rfl⟩
      exact u.ne_zero
    · intro h
      exact ⟨Units.mk0 a h, rfl⟩
  rw [this]
  exact isOpen_compl_singleton

theorem isOpenMap_normUnits_of_isOpen_range
    (hHo : IsOpen ((normUnits F E).range : Set Fˣ)) : IsOpenMap (normUnits F E) := by
  have : LocallyCompactSpace (normUnits F E).range := hHo.locallyCompactSpace
  have hc : Continuous (normUnits F E).rangeRestrict :=
    (continuous_normUnits F E).subtype_mk _
  have ho : IsOpenMap (normUnits F E).rangeRestrict :=
    MonoidHom.isOpenMap_of_sigmaCompact _ (normUnits F E).rangeRestrict_surjective hc
  exact hHo.isOpenMap_subtype_val.comp ho

theorem eventually_exists_norm_eq : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (t₀ : Eˣ) (T : Set Eˣ), T ∈ 𝓝 t₀ → ∀ᶠ a in 𝓝 (Algebra.norm F (t₀ : E)), ∃ t ∈ T, Algebra.norm F (t : E) = a := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ t₀ T hT
  have hopen : IsOpenMap (normUnits F E) := isOpenMap_normUnits_of_isOpen_range
    (GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.isOpen_range_normUnits (K := F) (E := E))
  have hF : IsOpenMap (fun t : Eˣ => ((normUnits F E t : Fˣ) : F)) :=
    isOpenEmbedding_units_val'.isOpenMap.comp hopen
  have hmem := hF.image_mem_nhds hT
  filter_upwards [hmem]
  rintro a ⟨t, ht, rfl⟩
  exact ⟨t, ht, rfl⟩

end GlobalTheory.CompanionTheory.NormLocal
