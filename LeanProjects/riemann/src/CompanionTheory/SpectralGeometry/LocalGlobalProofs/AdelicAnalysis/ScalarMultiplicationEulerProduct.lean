import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LinearChangeEulerProductStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PfK

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R]

theorem repr_inclR_mul {d : ℕ} (b : Module.Basis (Fin d) F E) (t : E) (y : R ⊗[F] E) :
    (fun k => (Algebra.TensorProduct.basis R b).repr (inclR R t * y) k) =
      (Algebra.leftMulMatrix b t).map (algebraMap F R) *ᵥ
        (fun k => (Algebra.TensorProduct.basis R b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => funext k; simp [Matrix.mulVec, dotProduct]
  | tmul r e =>
    have h1 : inclR R t * (r ⊗ₜ[F] e) = r ⊗ₜ[F] (t * e) := by
      simp [inclR, Algebra.TensorProduct.tmul_mul_tmul]
    have h2 : (fun j => ((Algebra.TensorProduct.basis R b).repr (r ⊗ₜ[F] e)) j) =
        r • (algebraMap F R ∘ b.repr e) := by
      funext j
      simp [Algebra.TensorProduct.basis_repr_tmul]
    rw [h1, h2, Matrix.mulVec_smul]
    funext k
    rw [Pi.smul_apply, ← RingHom.map_mulVec, Algebra.leftMulMatrix_mulVec_repr]
    simp [Algebra.TensorProduct.basis_repr_tmul]
  | add y1 y2 h1 h2 =>
    have e1 : (fun k => ((Algebra.TensorProduct.basis R b).repr (y1 + y2)) k) =
        (fun k => ((Algebra.TensorProduct.basis R b).repr y1) k) +
          (fun k => ((Algebra.TensorProduct.basis R b).repr y2) k) := by
      funext k; simp
    have e2 : (fun k => ((Algebra.TensorProduct.basis R b).repr (inclR R t * (y1 + y2))) k) =
        (fun k => ((Algebra.TensorProduct.basis R b).repr (inclR R t * y1)) k) +
          (fun k => ((Algebra.TensorProduct.basis R b).repr (inclR R t * y2)) k) := by
      funext k; simp [mul_add]
    rw [e1, e2, Matrix.mulVec_add, h1, h2]

variable [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R]
  [MeasurableSpace R] [BorelSpace R]

theorem map_inclR_mul [Module.Finite F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (t : E) (c : ℝ≥0)
    (h : ∀ μ : Measure (Fin d → R), μ.IsAddHaarMeasure →
      μ.map (fun x => (Algebra.leftMulMatrix b t).map (algebraMap F R) *ᵥ x) = c • μ)
    (μ : Measure (R ⊗[F] E)) (hμ : μ.IsAddHaarMeasure) :
    μ.map (fun y => inclR R t * y) = c • μ := by
  have : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (R ⊗[F] E) := TopK.isTopRing R
  let L : (R ⊗[F] E) ≃L[R] (Fin d → R) :=
    { toLinearEquiv := (Algebra.TensorProduct.basis R b).equivFun,
      continuous_toFun := (TopK.coordHomeo R b).continuous,
      continuous_invFun := (TopK.coordHomeo R b).symm.continuous }
  have hL : ∀ y, L y = fun k => ((Algebra.TensorProduct.basis R b).repr y) k := fun y =>
    Module.Basis.equivFun_apply _ _
  have : (μ.map L).IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  have hν := h (μ.map L) inferInstance
  have hA : Continuous fun x : Fin d → R => (Algebra.leftMulMatrix b t).map (algebraMap F R) *ᵥ x :=
    continuous_const.matrix_mulVec continuous_id
  have hmul : (fun y => inclR R t * y) =
      L.symm ∘ (fun x => (Algebra.leftMulMatrix b t).map (algebraMap F R) *ᵥ x) ∘ L := by
    funext y
    apply L.injective
    simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    rw [hL, hL]
    exact repr_inclR_mul R b t y
  have hid : (μ.map L).map L.symm = μ := by
    rw [Measure.map_map L.symm.continuous.measurable L.continuous.measurable]
    have : (L.symm ∘ L) = id := funext fun y => L.symm_apply_apply y
    rw [this, Measure.map_id]
  rw [hmul, ← Measure.map_map L.symm.continuous.measurable (hA.comp L.continuous).measurable,
    ← Measure.map_map hA.measurable L.continuous.measurable, hν, Measure.map_smul, hid]

end

end GlobalTheory.CompanionTheory.SW.PfK

open GlobalTheory.CompanionTheory.SW.PfK in

theorem GlobalTheory.CompanionTheory.SW.map_inclR_prodFormula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ t : E, t ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (Ainf F ⊗[F] E), μ.IsAddHaarMeasure → μ.map (fun y => inclR (Ainf F) t * y) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (Fv F v ⊗[F] E), μ.IsAddHaarMeasure → μ.map (fun y => inclR (Fv F v) t * y) = c v • μ) := by
  intro F E _ _ _ _ _ σ hCM t ht
  have hfin : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨cinf, c, hU, hinf, hv⟩ := T.addHaar_map_mulVec_eq_smul_at_all_places F (Fin (Module.finrank F E))
    (Algebra.leftMulMatrix (Module.finBasis F E) t) (by
      rw [← Algebra.norm_eq_matrix_det]
      exact Algebra.norm_ne_zero_iff.2 ht)
  refine ⟨cinf, c, hU, fun μ hμ => ?_, fun v μ hμ => ?_⟩
  · have : BorelSpace (Ainf F) := ⟨rfl⟩
    exact map_inclR_mul (Ainf F) (Module.finBasis F E) t cinf hinf μ hμ
  · have : SecondCountableTopology (Fv F v) := (LocFv.isLocR_Fv F v).2.2.1
    have : BorelSpace (Fv F v) := ⟨rfl⟩
    exact map_inclR_mul (Fv F v) (Module.finBasis F E) t (c v) (hv v) μ hμ
