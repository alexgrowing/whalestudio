import Mathlib
import GroundTheory.GlobalFields.TateThesis.TraceLatticeEuclidean
import GroundTheory.GlobalFields.TateThesis.LatticePoisson

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical RealInnerProductSpace FourierTransform SchwartzMap nonZeroDivisors

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem idealLattice_summable_norm (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (f : 𝓢(mixedSpace K, ℂ))
    (a : mixedSpace K) : Summable fun α : idealLattice K I => ‖f (α + a)‖ := by
  simpa [add_comm] using summable_norm_comp_add (idealLattice K I) f a

theorem traceDualIdeal_summable_norm (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(mixedSpace K, ℂ)) (a : mixedSpace K) :
    Summable fun β : idealLattice K (traceDualIdeal K I) =>
      ‖mixedFourier K f β * 𝐞 (mixedTraceForm K β a)‖ := by
  have h := summable_norm_comp_add (idealLattice K (traceDualIdeal K I)) (mixedFourierSchwartz K f) 0
  simpa [norm_mul, Circle.norm_coe, mixedFourierSchwartz_apply] using h

theorem idealLattice_poisson_summation (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(mixedSpace K, ℂ)) (a : mixedSpace K) :
    ∑' α : idealLattice K I, f (α + a) =
      (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) * √|(discr K : ℝ)|)⁻¹ •
        ∑' β : idealLattice K (traceDualIdeal K I),
          mixedFourier K f β * 𝐞 (mixedTraceForm K β a) := by
  set L := euclideanIdealLattice K I
  set F : 𝓢(euclidean.mixedSpace K, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean K).symm f
  have hF : (F : euclidean.mixedSpace K → ℂ) = f ∘ (mixedToEuclidean K).symm := rfl
  have h := lattice_poisson_summation L F (mixedToEuclidean K a)

  let eL : idealLattice K I ≃ L :=
    { toFun := fun α => ⟨mixedToEuclidean K α, by
        rw [mem_euclideanIdealLattice, ContinuousLinearEquiv.symm_apply_apply]; exact α.2⟩
      invFun := fun ℓ => ⟨(mixedToEuclidean K).symm ℓ, ℓ.2⟩
      left_inv := fun α => Subtype.ext (ContinuousLinearEquiv.symm_apply_apply _ _)
      right_inv := fun ℓ => Subtype.ext (ContinuousLinearEquiv.apply_symm_apply _ _) }

  let eD : idealLattice K (traceDualIdeal K I) ≃ dualLattice L :=
    { toFun := fun β => ⟨mixedToEuclideanConj K β, by
        rw [dualLattice_euclideanIdealLattice, mem_euclideanConjIdealLattice,
          ContinuousLinearEquiv.symm_apply_apply]; exact β.2⟩
      invFun := fun μ => ⟨(mixedToEuclideanConj K).symm μ, by
        have hμ : (μ : euclidean.mixedSpace K) ∈ euclideanConjIdealLattice K (traceDualIdeal K I) := by
          rw [← dualLattice_euclideanIdealLattice]
          exact μ.2
        exact hμ⟩
      left_inv := fun β => Subtype.ext (ContinuousLinearEquiv.symm_apply_apply _ _)
      right_inv := fun μ => Subtype.ext (ContinuousLinearEquiv.apply_symm_apply _ _) }
  have hlhs : ∑' ℓ : L, F (ℓ + mixedToEuclidean K a) = ∑' α : idealLattice K I, f (α + a) := by
    rw [← Equiv.tsum_eq eL]
    refine tsum_congr fun α => ?_
    change f ((mixedToEuclidean K).symm (mixedToEuclidean K α + mixedToEuclidean K a)) = _
    rw [← map_add, ContinuousLinearEquiv.symm_apply_apply]
  have hrhs : ∑' μ : dualLattice L, 𝓕 (F : euclidean.mixedSpace K → ℂ) μ *
      𝐞 ⟪(μ : euclidean.mixedSpace K), mixedToEuclidean K a⟫ =
      ∑' β : idealLattice K (traceDualIdeal K I),
        mixedFourier K f β * 𝐞 (mixedTraceForm K β a) := by
    rw [← Equiv.tsum_eq eD]
    refine tsum_congr fun β => ?_
    change 𝓕 (F : euclidean.mixedSpace K → ℂ) (mixedToEuclideanConj K β) *
      𝐞 ⟪mixedToEuclideanConj K β, mixedToEuclidean K a⟫ = _
    rw [hF, ← mixedFourier_eq, inner_mixedToEuclideanConj_mixedToEuclidean]
  rw [hlhs, hrhs, covolume_euclideanIdealLattice] at h
  exact h

end

end GroundTheory.Global
