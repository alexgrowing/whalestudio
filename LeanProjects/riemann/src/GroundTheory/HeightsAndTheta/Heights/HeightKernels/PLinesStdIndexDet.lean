import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix
open scoped Pointwise

noncomputable section

namespace KLinesStdIndexDet

theorem span_toAddSubgroup_eq_closure (K : Type) [Field K] [NumberField K] (k : ℕ)
    (f : (Fin k → K) →ₗ[K] (Fin k → K)) :
    (Submodule.span (𝓞 K) (Set.range fun j : Fin k => f (Pi.single j 1))).toAddSubgroup =
      AddSubgroup.closure (Set.range fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × Fin k =>
        integralBasis K p.1 • f (Pi.single p.2 1)) := by
  rw [← Submodule.span_int_eq_addSubgroupClosure]
  have hs : Submodule.span ℤ (Set.range (RingOfIntegers.basis K)) = ⊤ :=
    (RingOfIntegers.basis K).span_eq
  have h := Submodule.span_smul_of_span_eq_top hs
    (Set.range fun j : Fin k => f (Pi.single j 1))
  have hr : (Set.range (RingOfIntegers.basis K) • Set.range fun j : Fin k => f (Pi.single j 1)) =
      Set.range fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × Fin k =>
        integralBasis K p.1 • f (Pi.single p.2 1) := by
    rw [Set.range_smul_range]
    congr 1
    funext p
    rw [integralBasis_apply, algebraMap_smul]
  rw [hr] at h
  rw [h]
  rfl

end KLinesStdIndexDet

open KLinesStdIndexDet in

theorem LinesStdIndexDet.proof (h1 : LinesGenIndexDet.Statement) : LinesStdIndexDet.Statement := by
  classical
  intro K _ _ k V hV
  let B0 : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 K) × Fin k) ℚ (Fin k → K) :=
    (integralBasis K).smulTower (Pi.basisFun K (Fin k))
  have hB0 : ∀ p, B0 p = integralBasis K p.1 • (Pi.single p.2 1 : Fin k → K) := by
    intro p
    simp only [B0, Module.Basis.smulTower_apply, Pi.basisFun_apply]
  let Ve : (Fin k → K) ≃ₗ[K] (Fin k → K) :=
    Matrix.toLinearEquiv' V (Matrix.invertibleOfIsUnitDet V (Ne.isUnit hV))
  have hVe : ∀ v, Ve v = V *ᵥ v := fun v => rfl
  let Vq : (Fin k → K) ≃ₗ[ℚ] (Fin k → K) := Ve.restrictScalars ℚ
  have hA : (stdLattice K k).toAddSubgroup = AddSubgroup.closure (Set.range B0) := by
    have := span_toAddSubgroup_eq_closure K k LinearMap.id
    simp only [LinearMap.id_apply] at this
    rw [stdLattice, this]
    exact congrArg (fun s => AddSubgroup.closure s)
      (congrArg Set.range (funext fun p => (hB0 p).symm))
  have hB : (Submodule.span (𝓞 K)
        (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K))).toAddSubgroup =
      AddSubgroup.closure (Set.range (B0.map Vq)) := by
    have := span_toAddSubgroup_eq_closure K k (Matrix.toLin' V)
    simp only [Matrix.toLin'_apply] at this
    rw [this]
    refine congrArg (fun s => AddSubgroup.closure s)
      (congrArg Set.range (funext fun p => ?_))
    rw [Module.Basis.map_apply, hB0]
    change _ = Ve _
    rw [map_smul, hVe]
  rw [h1 (Fin k → K) _ B0 (B0.map Vq) _ _ hA hB]
  have hdet : B0.det (B0.map Vq) = Algebra.norm ℚ V.det := by
    have hc : (⇑(B0.map Vq) : _ → Fin k → K) = (Vq : (Fin k → K) →ₗ[ℚ] (Fin k → K)) ∘ B0 := by
      funext p
      rfl
    rw [hc, Module.Basis.det_comp, Module.Basis.det_self, mul_one]
    have hq : (Vq : (Fin k → K) →ₗ[ℚ] (Fin k → K)) = (Matrix.toLin' V).restrictScalars ℚ := by
      ext v
      rfl
    rw [hq, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  rw [hdet]

end

end GroundTheory.Heights₂.Heights
