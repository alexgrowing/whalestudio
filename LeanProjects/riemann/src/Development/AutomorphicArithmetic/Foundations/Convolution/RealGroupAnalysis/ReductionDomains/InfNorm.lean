import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import GroundTheory.AutomorphicForms.NormDetDiagUnitsPosRealToUnits
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus
import GroundTheory.AutomorphicForms.GL2Classical.GrowthReduction

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

namespace UpperTheory.ConvolutionTheory.R2.M

variable {F : Type} [Field F] [NumberField F]

private theorem int_det {R : Type*} [CommRing R] (S : Subring R) {m : Matrix (Fin 2) (Fin 2) R}
    (h : ∀ i j, m i j ∈ S) : m.det ∈ S := by
  rw [Matrix.det_fin_two]
  exact S.sub_mem (S.mul_mem (h 0 0) (h 1 1)) (S.mul_mem (h 0 1) (h 1 0))

private theorem fin_int {k : GL (Fin 2) (A F)} (hk : k ∈ Reduction.maxCompact (K := F) (n := 2))
    (v : HeightOneSpectrum (𝓞 F)) :
    (((Matrix.GeneralLinearGroup.det k : (A F)ˣ) : A F)).2 v ∈
      (ValuativeRel.valuation (v.adicCompletion F)).integer := by
  have h := ((GLnLocal.mem_integralGL_iff _ _).1 (hk.2 v)).1
  have e := GL2Classical.det_finAt_eq v k
  have e' : (((Matrix.GeneralLinearGroup.det k : (A F)ˣ) : A F)).2 v =
      ((Reduction.finAt v k : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det := e
  rw [e']
  exact int_det _ h

private theorem inf_norm {k : GL (Fin 2) (A F)} (hk : k ∈ Reduction.maxCompact (K := F) (n := 2))
    (w : InfinitePlace F) : ‖(((Matrix.GeneralLinearGroup.det k : (A F)ˣ) : A F)).1 w‖ = 1 := by
  have e := GL2Classical.det_infAt_eq w k
  have e' : (((Matrix.GeneralLinearGroup.det k : (A F)ˣ) : A F)).1 w =
      ((Reduction.infAt w k : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det := e
  rw [e']
  exact Reduction.norm_det_infAt_of_mem_maxCompact hk w

private theorem dM_mem (t : (A F)ˣ) (h1 : ∀ w : InfinitePlace F, ‖((t : A F)).1 w‖ = 1)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 F), ((t : A F)).2 v ∈
      (ValuativeRel.valuation (v.adicCompletion F)).integer)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 F), (((t⁻¹ : (A F)ˣ) : A F)).2 v ∈
      (ValuativeRel.valuation (v.adicCompletion F)).integer) :
    dM t ∈ Reduction.maxCompact (K := F) (n := 2) := by
  refine ⟨fun w => ?_, fun v => ?_⟩
  · intro y
    have key : Reduction.euclidNorm (y ᵥ* ((Reduction.infAt w (dM t) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion)) ^ 2 = Reduction.euclidNorm y ^ 2 := by
      rw [Reduction.euclidNorm_sq, Reduction.euclidNorm_sq, Fin.sum_univ_two, Fin.sum_univ_two]
      have a0 : (y ᵥ* ((Reduction.infAt w (dM t) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion)) 0 = y 0 := by
        simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, dM]
        exact Or.inr rfl
      have a1 : (y ᵥ* ((Reduction.infAt w (dM t) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion)) 1 = y 1 * ((t : A F)).1 w := by
        simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, dM]
        exact Or.inr rfl
      rw [a0, a1, norm_mul, h1 w, mul_one]
    exact (sq_eq_sq₀ (Reduction.euclidNorm_nonneg _) (Reduction.euclidNorm_nonneg _)).1 key
  · rw [GLnLocal.mem_integralGL_iff, ← Reduction.finAt_inv]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [dM, Subring.zero_mem, Subring.one_mem, h2 v]
    · fin_cases i <;> fin_cases j <;> simp [dM, h3 v]

end UpperTheory.ConvolutionTheory.R2.M

theorem UpperTheory.ConvolutionTheory.R2.M.detK :
    ∀ (F : Type) [Field F] [NumberField F], ∀ k ∈ Reduction.maxCompact (K := F) (n := 2), dM (Matrix.GeneralLinearGroup.det k) ∈ Reduction.maxCompact (K := F) (n := 2) ∧ ab (Matrix.GeneralLinearGroup.det k) = 1 := by
  intro F _ _ k hk
  refine ⟨dM_mem _ (inf_norm hk) (fin_int hk) fun v => ?_, ?_⟩
  · have := fin_int (inv_mem hk) v
    rwa [map_inv] at this
  · have := GJGlobal.Modulus.ideleModule_det_of_mem_maxCompact' hk
    simp [ab, this]
