import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeSpanProjectionPreservesFiniteDimInvariantSub
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableOfIsGKSub
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typeSpanProjection_preserves_finiteDim_invariant_subspace : ∀ {M ι : Type} [AddCommGroup M] [Module ℂ M] (b : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (G : Submodule ℂ M) (ρ : ι → M →ₗ[ℂ] M)
    (inv : ι → ι), (∀ x ∈ G, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ G, ∀ y ∈ G, star (b x y) = b y x) →
    (∀ i, ∀ x ∈ G, ρ i x ∈ G) → (∀ i, ∀ x ∈ G, ∀ y ∈ G, b (ρ i x) y = b x (ρ (inv i) y)) →
    (∀ F : Submodule ℂ M, F ≤ G → FiniteDimensional ℂ F →
      ∃ π : M →ₗ[ℂ] M, (∀ x, π x ∈ F) ∧ ∀ x, ∀ f ∈ F, b (π x) f = b x f) →
    ∀ (Y₀ : Submodule ℂ M) (e : M →ₗ[ℂ] M), (∀ x, e x ∈ GlobalTheory.KTypeProj.typeSpan ρ Y₀ G) →
    (∀ x, ∀ f ∈ GlobalTheory.KTypeProj.typeSpan ρ Y₀ G, b (e x) f = b x f) →
    ∀ Y : Submodule ℂ M, FiniteDimensional ℂ Y → Y ≤ G → (∀ i, ∀ y ∈ Y, ρ i y ∈ Y) → ∀ x ∈ Y, e x ∈ Y := by
  first | exact @GlobalTheory.KTypeProj.typeSpan_proj_mem | exact GlobalTheory.KTypeProj.typeSpan_proj_mem | (intros; apply GlobalTheory.KTypeProj.typeSpan_proj_mem <;> assumption)
