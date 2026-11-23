import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
import GroundTheory.AutomorphicForms.MeasuresModulus
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open MeasureTheory
open scoped NNReal Pointwise

namespace GlobalTheory.DetScale

theorem integral_comp_linearEquiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V] [TopologicalSpace V] [IsModuleTopology k V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (L : V ≃ₗ[k] V) (f : V → ℂ) :
    ∫ y, f (L y) ∂μ = (((distribHaarChar k (LinearEquiv.det L) : ℝ≥0) : ℝ) : ℂ)⁻¹ * ∫ y, f y ∂μ := by
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup k V
  let n := Module.finrank k V
  let e0 : V ≃ₗ[k] (Fin n → k) := (Module.finBasis k V).equivFun
  let e : V ≃L[k] (Fin n → k) :=
    { e0 with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e0.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e0.symm.toLinearMap }
  borelize (Fin n → k)
  let ν : Measure (Fin n → k) := μ.map e
  haveI : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let L' : (Fin n → k) ≃ₗ[k] (Fin n → k) := (e0.symm.trans L).trans e0
  set c : ℝ≥0 := distribHaarChar k (LinearEquiv.det L) with hc
  have hd : distribHaarChar (Fin n → k) L' = c := by
    rw [GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq, LinearEquiv.det_conj]
  have hc0 : c ≠ 0 := (distribHaarChar_pos (A := k) (g := LinearEquiv.det L)).ne'
  let Lh : V ≃ₜ V :=
    { L.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap L.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap }
  have hν : ∀ s : Set V, ν (e '' s) = μ s := fun s => by
    have h := e.toHomeomorph.toMeasurableEquiv.map_apply (μ := μ) (e '' s)
    refine h.trans ?_
    congr 1
    exact Set.preimage_image_eq s e.injective
  have hm : μ.map Lh.toMeasurableEquiv = c⁻¹ • μ := by
    ext s _
    rw [MeasurableEquiv.map_apply, Measure.smul_apply, ← hν, ← hν s]
    have h := distribHaarChar_mul ν L' (e '' (Lh ⁻¹' s))
    have hs : L' • (e '' (Lh ⁻¹' s)) = e '' s := by
      ext z
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨L y, hy, ?_⟩
        simp [L', e, LinearEquiv.smul_def]
      · rintro ⟨y, hy, rfl⟩
        refine ⟨e (L.symm y), ⟨L.symm y, ?_, rfl⟩, ?_⟩
        · simpa [Lh] using hy
        · simp [L', e, LinearEquiv.smul_def]
    rw [hs, hd] at h
    rw [← h, ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hc0,
      ENNReal.coe_one, one_mul]
    rfl
  have e1 : ∫ y, f (L y) ∂μ = ∫ y, f (Lh.toMeasurableEquiv y) ∂μ := rfl
  rw [e1, ← integral_map_equiv, hm, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  push_cast
  rfl

theorem integral_comp_matrix : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (a b : ℕ) (L : Matrix (Fin a) (Fin b) F →ₗ[F] Matrix (Fin a) (Fin b) F) (hL : LinearMap.det L ≠ 0)
    (φ : Matrix (Fin a) (Fin b) F → ℂ) (μ : @MeasureTheory.Measure (Matrix (Fin a) (Fin b) F) (borel _)),
    @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∫ x, φ (L x) ∂μ = ((((MeasureTheory.distribHaarChar F (Units.mk0 _ hL) : NNReal) : ℝ) : ℂ))⁻¹ * ∫ x, φ x ∂μ := by
  intro F _ _ _ _ a b L hL φ μ hμ
  letI : MeasurableSpace (Matrix (Fin a) (Fin b) F) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin b) F) := ⟨rfl⟩
  haveI : IsModuleTopology F (Matrix (Fin a) (Fin b) F) :=
    show IsModuleTopology F (Fin a → Fin b → F) from inferInstance
  let Le := LinearMap.equivOfDetNeZero L hL
  have hdet : LinearEquiv.det Le = Units.mk0 _ hL := by
    ext
    rw [LinearEquiv.coe_det, Units.val_mk0]
    rfl
  have h := integral_comp_linearEquiv (k := F) μ Le φ
  rw [hdet] at h
  exact h

end GlobalTheory.DetScale
