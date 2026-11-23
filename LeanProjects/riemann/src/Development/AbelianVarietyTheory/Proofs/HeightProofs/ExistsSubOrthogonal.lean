import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV

namespace GlobalTheory.OrthogonalProjectionPoly

open MeasureTheory

theorem exists_sub_orthogonal {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ q ∈ V, Continuous q) (p : X → ℂ) (hp : Continuous p) :
    ∃ p' ∈ V, ∀ q ∈ V, ∫ x, star (q x) * (p x - p' x) ∂μ = 0 := by
  classical
  let j : V →ₗ[ℂ] C(X, ℂ) :=
    { toFun := fun q => ⟨q, hV q q.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let T : V →ₗ[ℂ] Lp ℂ 2 μ := (ContinuousMap.toLp 2 μ ℂ : C(X, ℂ) →L[ℂ] Lp ℂ 2 μ).toLinearMap ∘ₗ j
  let W : Submodule ℂ (Lp ℂ 2 μ) := LinearMap.range T
  have : FiniteDimensional ℂ W := LinearMap.finiteDimensional_range T
  let P : C(X, ℂ) := ⟨p, hp⟩
  obtain ⟨p', hp'⟩ := LinearMap.mem_range.1 (W.starProjection_apply_mem (ContinuousMap.toLp 2 μ ℂ P))
  refine ⟨p', p'.2, fun q hq => ?_⟩
  have h0 := W.starProjection_inner_eq_zero (ContinuousMap.toLp 2 μ ℂ P) (T ⟨q, hq⟩) ⟨⟨q, hq⟩, rfl⟩
  rw [← hp'] at h0
  have h1 : ContinuousMap.toLp 2 μ ℂ P - T p' = ContinuousMap.toLp 2 μ ℂ (P - j p') := by
    rw [map_sub]
    rfl
  rw [h1] at h0
  have h2 : inner ℂ (ContinuousMap.toLp 2 μ ℂ (P - j p')) (T ⟨q, hq⟩) =
      ∫ x, q x * (starRingEnd ℂ) (p x - (p' : X → ℂ) x) ∂μ :=
    ContinuousMap.inner_toLp μ (P - j p') (j ⟨q, hq⟩)
  rw [h2] at h0
  calc ∫ x, star (q x) * (p x - (p' : X → ℂ) x) ∂μ
      = ∫ x, (starRingEnd ℂ) (q x * (starRingEnd ℂ) (p x - (p' : X → ℂ) x)) ∂μ := by
        congr 1
        funext x
        rw [map_mul, Complex.conj_conj, starRingEnd_apply, _root_.mul_comm]
    _ = (starRingEnd ℂ) (∫ x, q x * (starRingEnd ℂ) (p x - (p' : X → ℂ) x) ∂μ) := integral_conj
    _ = 0 := by rw [h0, map_zero]

theorem exists_proj_polyV : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (p : ↥(Formalism.REAL.KG ε) → ℂ), Continuous p →
    ∃ p' ∈ GlobalTheory.KFourier.polyV ε d, ∀ q ∈ GlobalTheory.KFourier.polyV ε d,
      ∫ (k : ↥(Formalism.REAL.KG ε)), Star.star (q k) * (p k - p' k) ∂ Formalism.REAL.muK ε = (0 : ℂ) := by
  intro n ε d p hp
  exact exists_sub_orthogonal (Formalism.REAL.muK ε) (GlobalTheory.KFourier.polyV ε d)
    (fun q hq => GlobalTheory.KFourier.continuous_of_mem hq) p hp

end GlobalTheory.OrthogonalProjectionPoly
