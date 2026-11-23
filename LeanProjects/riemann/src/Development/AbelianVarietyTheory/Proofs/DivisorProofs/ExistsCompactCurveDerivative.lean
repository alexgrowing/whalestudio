import Development.AbelianVarietyTheory.Definitions.Divisors.Tpr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.WigCurve

theorem exists_unitary_matrix_curve (E : Type) [Field E] [NumberField E] (a : ℕ) (Z : Matrix (Fin a) (Fin a) (Cinf E))
    (hZ : star Z = -Z) :
    ∃ f : ℝ → Matrix (Fin a) (Fin a) (Cinf E), (∀ t, f t ∈ unitary (Matrix (Fin a) (Fin a) (Cinf E))) ∧
      f 0 = 1 ∧ HasDerivAt (fun t => toL (f t)) (toL Z) 0 := by
  have hcs : ContinuousStar (Matrix (Fin a) (Fin a) (Cinf E)) := inferInstance
  letI : NormedRing (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin a) (Fin a) (Cinf E)) := NormedAlgebra.restrictScalars ℚ ℝ _
  refine ⟨fun t => NormedSpace.exp (t • Z), fun t => ?_, by simp, ?_⟩
  · refine @NormedSpace.exp_mem_unitary_of_mem_skewAdjoint _ _ _ _ _ ⟨hcs.continuous_star⟩ _ ?_
    rw [skewAdjoint.mem_iff, star_smul, hZ, star_trivial, smul_neg]
  · have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ)
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
    let L : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
      LinearMap.toContinuousLinearMap
        { toFun := fun x => toL x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem exists_kinf_curve_tangent : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (Z : Matrix (Fin a) (Fin a) (Cinf E)), star Z = -Z → ∃ c : ℝ → Kinf E a, c 0 = 1 ∧ HasDerivAt (fun t => toL (c t).1) (toL Z) 0 := by
  intro E _ _ a Z hZ
  obtain ⟨f, hu, h0, hd⟩ := exists_unitary_matrix_curve E a Z hZ
  exact ⟨fun t => ⟨f t, hu t⟩, Subtype.ext h0, hd⟩

end GlobalTheory.WigCurve

end
