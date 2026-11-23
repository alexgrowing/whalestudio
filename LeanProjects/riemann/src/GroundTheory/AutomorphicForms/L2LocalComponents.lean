import Mathlib
import GroundTheory.AutomorphicForms.L2LocalComponents.LocalComponents
import GroundTheory.AutomorphicForms.L2LocalComponents.NonEmpty

open MeasureTheory

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

open CuspidalSpectrum

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

namespace CuspidalAutomorphicRepresentation

variable {μ : Measure (Reduction.normOneGL K n)} [μ.IsHaarMeasure]

def ofL2Summand (V : Submodule ℂ (CuspL2 μ)) [CompleteSpace V] (hV : (cuspRepT μ).IsInvariant V)
    (hirr : ((cuspRepT μ).restrict V hV).IsIrreducible) : CuspidalAutomorphicRepresentation K n :=
  ofSummand V hV hirr (summandCuspForms_ne_bot μ V hV hirr)

@[simp] theorem carrier_ofL2Summand (V : Submodule ℂ (CuspL2 μ)) [CompleteSpace V]
    (hV : (cuspRepT μ).IsInvariant V) (hirr : ((cuspRepT μ).restrict V hV).IsIrreducible) :
    (ofL2Summand V hV hirr).carrier = summandCuspForms V := rfl

theorem topologicalClosure_map_ofL2Summand (V : Submodule ℂ (CuspL2 μ)) [CompleteSpace V]
    (hV : (cuspRepT μ).IsInvariant V) (hirr : ((cuspRepT μ).restrict V hV).IsIrreducible) :
    ((ofL2Summand V hV hirr).carrier.map (cuspVecL μ)).topologicalClosure = V :=
  topologicalClosure_map_ofSummand V hV hirr _

theorem nonempty_adelicDecomposition_ofL2Summand (V : Submodule ℂ (CuspL2 μ)) [CompleteSpace V]
    (hV : (cuspRepT μ).IsInvariant V) (hirr : ((cuspRepT μ).restrict V hV).IsIrreducible) :
    Nonempty (AdelicDecomposition (ofL2Summand V hV hirr).toModule) :=
  (ofL2Summand V hV hirr).nonempty_adelicDecomposition

end CuspidalAutomorphicRepresentation

open CuspidalAutomorphicRepresentation

variable {μ : Measure (Reduction.normOneGL K n)} [μ.IsHaarMeasure]

def L2SummandIsSupercuspidalAt (V : Submodule ℂ (CuspL2 μ)) [CompleteSpace V] (hV : (cuspRepT μ).IsInvariant V)
    (hirr : ((cuspRepT μ).restrict V hV).IsIrreducible)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : Prop :=
  (ofL2Summand V hV hirr).IsSupercuspidalAt v

end AutomorphicForm

namespace CuspidalSpectrum

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

variable (μ : Measure (Reduction.normOneGL K n)) [μ.IsHaarMeasure]

theorem exists_cuspForm_mem_of_ne_bot {W : Submodule ℂ (CuspL2 μ)} (hWc : IsClosed (W : Set (CuspL2 μ)))
    (hW : (cuspRepT μ).IsInvariant W) (hW0 : W ≠ ⊥) :
    ∃ φ ∈ centralCuspForms K n, φ ≠ 0 ∧ cuspVecL μ φ ∈ W := by
  obtain ⟨V, hVmin, hVW⟩ := UnitaryRep.exists_isMinimal_le (π := cuspRepT μ) (μ := μ)
    (fun f => isCompactOperator_cuspRep μ f) hWc hW hW0
  have : CompleteSpace V := hVmin.1.completeSpace_coe
  have hirr := UnitaryRep.isIrreducible_restrict_of_isMinimal hVmin.2.1 hVmin
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (summandCuspForms_ne_bot μ V hVmin.2.1 hirr)
  exact ⟨φ, hφ.1, hφ0, hVW hφ.2⟩

theorem topologicalClosure_map_centralCuspForms :
    ((centralCuspForms K n).map (cuspVecL μ)).topologicalClosure = ⊤ := by
  set Y := ((centralCuspForms K n).map (cuspVecL μ)).topologicalClosure
  have hYc : IsClosed (Y : Set (CuspL2 μ)) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace Y := hYc.completeSpace_coe
  have hY : (cuspRepT μ).IsInvariant Y :=
    isInvariant_topologicalClosure_map μ le_rfl (fun X φ hφ => ρ_mem_centralCuspForms X hφ)
      (fun k φ hφ => σ_mem_centralCuspForms k hφ) (fun g φ hφ => finRepCusp_mem_centralCuspForms g hφ)
  rw [← Submodule.orthogonal_eq_bot_iff]
  by_contra h0
  obtain ⟨φ, hφ, hφ0, hφY⟩ := exists_cuspForm_mem_of_ne_bot μ (Submodule.isClosed_orthogonal Y)
    hY.orthogonal h0
  have hmem : cuspVecL μ φ ∈ Y := Submodule.le_topologicalClosure _ ⟨φ, hφ, rfl⟩
  have h1 := Submodule.inner_right_of_mem_orthogonal hmem hφY
  rw [inner_self_eq_zero] at h1
  exact hφ0 (eq_zero_of_cuspVecL_eq_zero hφ h1)

end CuspidalSpectrum

end

end GroundTheory.Automorphic
