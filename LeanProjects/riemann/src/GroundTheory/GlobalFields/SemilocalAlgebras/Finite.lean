import Mathlib
import GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
import GroundTheory.GlobalFields.SemilocalAlgebras.Approximation
import GroundTheory.GlobalFields.SemilocalAlgebras.LocalDegree

namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Module

noncomputable section

namespace SemiLocal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (L) (v : HeightOneSpectrum (𝓞 K))

abbrev CompletionsOver : Type _ := (w : PlacesOver L v) → w.1.adicCompletion L

def tensorMap : v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K] CompletionsOver L v :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (IsScalarTower.toAlgHom K L _)
    (fun _ _ ↦ Commute.all _ _)

@[simp] theorem tensorMap_tmul (a : v.adicCompletion K) (x : L) :
    tensorMap L v (a ⊗ₜ x) =
      algebraMap (v.adicCompletion K) (CompletionsOver L v) a * algebraMap L _ x := by
  simp [tensorMap]

theorem denseRange_algebraMap_completionsOver :
    DenseRange (algebraMap L (CompletionsOver L v)) :=
  denseRange_algebraMap_pi (fun w : PlacesOver L v ↦ w.1) Subtype.val_injective

open scoped Valued in
theorem tensorMap_surjective : Function.Surjective (tensorMap L v) := by
  have hclosed : IsClosed (LinearMap.range (tensorMap L v).toLinearMap :
      Set (CompletionsOver L v)) :=
    Submodule.closed_of_finiteDimensional _
  have hdense : Dense (Set.range (tensorMap L v)) := by
    refine (denseRange_algebraMap_completionsOver L v).mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by simp⟩
  rw [LinearMap.coe_range] at hclosed
  have h2 : closure (Set.range (tensorMap L v)) = Set.range (tensorMap L v) := hclosed.closure_eq
  rw [← Set.range_eq_univ, ← h2, hdense.closure_eq]

theorem sum_finrank_le :
    ∑ w : PlacesOver L v, finrank (v.adicCompletion K) (w.1.adicCompletion L) ≤ finrank K L := by
  rw [← Module.finrank_pi_fintype]
  calc _ ≤ finrank (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) :=
        LinearMap.finrank_le_finrank_of_surjective (f := (tensorMap L v).toLinearMap)
          (tensorMap_surjective L v)
    _ = finrank K L := Module.finrank_baseChange

theorem sum_ramificationIdx_mul_inertiaDeg :
    ∑ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) * w.1.asIdeal.inertiaDeg (𝓞 K) =
      finrank K L := by
  have := v.isPrime
  rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L,
    ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 L)]
  exact Fintype.sum_equiv (placesOverEquiv L v) _ _ (fun _ ↦ rfl)

theorem sum_finrank_eq :
    ∑ w : PlacesOver L v, finrank (v.adicCompletion K) (w.1.adicCompletion L) = finrank K L := by
  refine le_antisymm (sum_finrank_le L v) ?_
  rw [← sum_ramificationIdx_mul_inertiaDeg L v]
  exact Finset.sum_le_sum fun w _ ↦ ramificationIdx_mul_inertiaDeg_le_finrank v w.1

theorem finrank_eq_ramificationIdx_mul_inertiaDeg (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    finrank (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) := by
  have h := (Finset.sum_eq_sum_iff_of_le
    (fun (w : PlacesOver L v) _ ↦ ramificationIdx_mul_inertiaDeg_le_finrank v w.1)).1
    (by rw [sum_ramificationIdx_mul_inertiaDeg, sum_finrank_eq])
  exact (h ⟨w, inferInstance⟩ (Finset.mem_univ _)).symm

theorem tensorMap_injective : Function.Injective (tensorMap L v) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (tensorMap L v).toLinearMap)
    (by rw [Module.finrank_baseChange, Module.finrank_pi_fintype, sum_finrank_eq])).2
    (tensorMap_surjective L v)

def tensorEquiv : v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K] CompletionsOver L v :=
  AlgEquiv.ofBijective (tensorMap L v) ⟨tensorMap_injective L v, tensorMap_surjective L v⟩

@[simp] theorem tensorEquiv_tmul (a : v.adicCompletion K) (x : L) :
    tensorEquiv L v (a ⊗ₜ x) =
      algebraMap (v.adicCompletion K) (CompletionsOver L v) a * algebraMap L _ x :=
  tensorMap_tmul L v a x

@[simp] theorem tensorEquiv_one_tmul (x : L) :
    tensorEquiv L v (1 ⊗ₜ x) = algebraMap L (CompletionsOver L v) x := by
  simp

def tensorMap' : L ⊗[K] v.adicCompletion K →ₐ[L] CompletionsOver L v :=
  Algebra.TensorProduct.lift (Algebra.ofId L _)
    (IsScalarTower.toAlgHom K (v.adicCompletion K) _) (fun _ _ ↦ Commute.all _ _)

@[simp] theorem tensorMap'_tmul (x : L) (a : v.adicCompletion K) :
    tensorMap' L v (x ⊗ₜ a) =
      algebraMap L (CompletionsOver L v) x * algebraMap (v.adicCompletion K) _ a := by
  simp [tensorMap']

theorem tensorMap'_eq_comp :
    ⇑(tensorMap' L v) = tensorEquiv L v ∘ Algebra.TensorProduct.comm K L (v.adicCompletion K) := by
  have : (tensorMap' L v).restrictScalars K =
      ((tensorEquiv L v).toAlgHom.restrictScalars K).comp
        (Algebra.TensorProduct.comm K L (v.adicCompletion K)).toAlgHom :=
    Algebra.TensorProduct.ext' fun x a ↦ by simp [mul_comm]
  exact congrArg DFunLike.coe this

def tensorEquiv' : L ⊗[K] v.adicCompletion K ≃ₐ[L] CompletionsOver L v :=
  AlgEquiv.ofBijective (tensorMap' L v) (by
    rw [tensorMap'_eq_comp]
    exact (tensorEquiv L v).bijective.comp (AlgEquiv.bijective _))

@[simp] theorem tensorEquiv'_tmul (x : L) (a : v.adicCompletion K) :
    tensorEquiv' L v (x ⊗ₜ a) =
      algebraMap L (CompletionsOver L v) x * algebraMap (v.adicCompletion K) _ a :=
  tensorMap'_tmul L v x a

theorem tensorEquiv'_tmul_mul (a : v.adicCompletion K) (y : L ⊗[K] v.adicCompletion K) :
    tensorEquiv' L v ((1 ⊗ₜ a) * y) =
      algebraMap (v.adicCompletion K) (CompletionsOver L v) a * tensorEquiv' L v y := by
  rw [map_mul, tensorEquiv'_tmul, map_one, one_mul]

open scoped Valued in

instance isModuleTopology_completionsOver :
    IsModuleTopology (v.adicCompletion K) (CompletionsOver L v) :=
  isModuleTopologyOfFiniteDimensional

def tensorHomeomorph [TopologicalSpace (v.adicCompletion K ⊗[K] L)]
    [IsModuleTopology (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)] :
    v.adicCompletion K ⊗[K] L ≃ₜ CompletionsOver L v where
  toEquiv := (tensorEquiv L v).toEquiv
  continuous_toFun :=
    IsModuleTopology.continuous_of_linearMap (tensorEquiv L v).toLinearEquiv.toLinearMap
  continuous_invFun := by
    have := IsModuleTopology.toContinuousAdd (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
    exact IsModuleTopology.continuous_of_linearMap (tensorEquiv L v).symm.toLinearEquiv.toLinearMap

@[simp] theorem tensorHomeomorph_apply [TopologicalSpace (v.adicCompletion K ⊗[K] L)]
    [IsModuleTopology (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)]
    (y : v.adicCompletion K ⊗[K] L) : tensorHomeomorph L v y = tensorEquiv L v y := rfl

end SemiLocal

end

end GroundTheory.Global
