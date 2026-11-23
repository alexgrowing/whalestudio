import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory.SnMass.VolN

theorem fractionalIdeal_basis_transport (K : Type) [Field K] [NumberField K] {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [MeasurableSpace W] [BorelSpace W] (μ : Measure W)
    (e : mixedEmbedding.mixedSpace K ≃L[ℝ] W) (he : MeasurePreserving e volume μ)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ W),
      (Submodule.span ℤ (Set.range b) : Set W) =
        (fun x : K => e (mixedEmbedding K x)) '' {x : K | x ∈ (J : FractionalIdeal (𝓞 K)⁰ K)} ∧
      μ (ZSpan.fundamentalDomain b) = ENNReal.ofReal (FractionalIdeal.absNorm
        (J : FractionalIdeal (𝓞 K)⁰ K) * (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
          Real.sqrt |(discr K : ℝ)|) := by
  set b₀ := mixedEmbedding.fractionalIdealLatticeBasis K J with hb₀
  refine ⟨_, inferInstance, b₀.map e.toLinearEquiv, ?_, ?_⟩
  · let f : mixedEmbedding.mixedSpace K →ₗ[ℤ] W := e.toLinearEquiv.toLinearMap.restrictScalars ℤ
    have hr : Set.range (b₀.map e.toLinearEquiv) = f '' Set.range b₀ := by
      rw [← Set.range_comp]; rfl
    have h0 : (Submodule.span ℤ (Set.range b₀) : Set (mixedEmbedding.mixedSpace K)) =
        mixedEmbedding K '' (J : Set K) := by
      ext x
      exact mixedEmbedding.mem_span_fractionalIdealLatticeBasis K J
    rw [hr, Submodule.span_image, Submodule.map_coe, h0, Set.image_image]
    rfl
  · have hfd : ZSpan.fundamentalDomain (b₀.map e.toLinearEquiv) =
        e '' ZSpan.fundamentalDomain b₀ := (ZSpan.map_fundamentalDomain b₀ e.toLinearEquiv).symm
    let E := e.toHomeomorph.toMeasurableEquiv
    have hE : MeasurePreserving E volume μ := he
    have h1 : μ (ZSpan.fundamentalDomain (b₀.map e.toLinearEquiv)) =
        volume (ZSpan.fundamentalDomain b₀) := by
      rw [← hE.measure_preimage_equiv, hfd]
      congr 1
      exact Set.preimage_image_eq _ e.injective
    rw [h1]
    have hfin : volume (ZSpan.fundamentalDomain b₀) ≠ ⊤ :=
      (ZSpan.fundamentalDomain_isBounded b₀).measure_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin, ← mixedEmbedding.covolume_idealLattice K J,
      ZLattice.covolume_eq_measure_fundamentalDomain _ _
        (mixedEmbedding.fundamentalDomain_idealLattice K J), measureReal_def]

end GlobalTheory.SnMass.VolN
