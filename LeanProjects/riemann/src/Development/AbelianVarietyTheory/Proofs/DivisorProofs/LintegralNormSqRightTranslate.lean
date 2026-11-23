import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import GroundTheory.LocalFields.LocalFourierHaar
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMapLinearScalingByDeterminant
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped NNReal ENNReal

namespace GlobalTheory.SplitFlip

theorem lintegral_mul_invT_sq : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ}
    (Φ : Matrix (Fin a) (Fin d) k → ℂ) (h : GL (Fin d) k),
    ∀ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖Φ (Y * (GlobalTheory.SplitFlip.invT h).1)‖ₑ ^ 2 ∂ν =
        ‖GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h) (a : ℂ)‖ₑ * ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν := by
  intro k _ _ _ _ a d Φ h ν hν
  letI mk : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  letI mM : MeasurableSpace (Matrix (Fin a) (Fin d) k) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin d) k) := ⟨rfl⟩
  haveI := hν
  set M : Matrix (Fin d) (Fin d) k := (invT h).1 with hM
  set M' : Matrix (Fin d) (Fin d) k := ((invT h)⁻¹).1
  have hMM' : M * M' = 1 := Units.mul_inv _
  have hM'M : M' * M = 1 := Units.inv_mul _
  let L : Matrix (Fin a) (Fin d) k ≃ᵐ Matrix (Fin a) (Fin d) k :=
    { toFun := fun Y => Y * M
      invFun := fun Y => Y * M'
      left_inv := fun Y => by simp [Matrix.mul_assoc, hMM']
      right_inv := fun Y => by simp [Matrix.mul_assoc, hM'M]
      measurable_toFun := (continuous_id.matrix_mul continuous_const).measurable
      measurable_invFun := (continuous_id.matrix_mul continuous_const).measurable }
  let f0 : Matrix (Fin a) (Fin d) k → (Fin a × Fin d → k) := fun Y p => Y p.1 p.2
  have hEc : Continuous f0 := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
  let g0 : (Fin a × Fin d → k) → Matrix (Fin a) (Fin d) k := fun f => Matrix.of fun i j => f (i, j)
  have hEsc : Continuous g0 :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
  let E : Matrix (Fin a) (Fin d) k ≃+ (Fin a × Fin d → k) :=
    { toFun := f0, invFun := g0, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_add' := fun _ _ => rfl }
  let EM : Matrix (Fin a) (Fin d) k ≃ᵐ (Fin a × Fin d → k) :=
    { toFun := f0, invFun := g0, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      measurable_toFun := hEc.measurable, measurable_invFun := hEsc.measurable }
  haveI hμ : (ν.map E).IsAddHaarMeasure := E.isAddHaarMeasure_map ν hEc hEsc
  let K : Matrix (Fin a × Fin d) (Fin a × Fin d) k := Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin a) (Fin a) k) Mᵀ
  have hK : ∀ Y, K *ᵥ f0 Y = f0 (Y * M) := by
    intro Y; funext p
    simp [K, f0, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, Matrix.mul_apply, mul_comm]
  have hdetK : K.det = (((gdet h)⁻¹ ^ a : kˣ) : k) := by
    rw [Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul, Matrix.det_transpose, Fintype.card_fin, ← gdet_invT]
    simp [M, gdet]
  have hu : K.det ≠ 0 := by rw [hdetK]; exact Units.ne_zero _
  have hlam : (Measure.addHaar : Measure k).map (fun x => algebraMap k k K.det * x) =
      (distribHaarChar k (gdet h) ^ a) • (Measure.addHaar : Measure k) := by
    have h2 := GlobalTheory.CompanionTheory.SW.DetScale.char_smul_map (Measure.addHaar : Measure k) ((gdet h)⁻¹ ^ a)
    rw [Algebra.algebraMap_self, RingHom.id_apply, hdetK]
    have hcd : distribHaarChar k (gdet h) ^ a * distribHaarChar k ((gdet h)⁻¹ ^ a) = 1 := by
      rw [map_pow, map_inv, ← mul_pow, mul_inv_cancel₀ distribHaarChar_pos.ne', one_pow]
    calc (Measure.addHaar : Measure k).map (fun x => (((gdet h)⁻¹ ^ a : kˣ) : k) * x)
        = (distribHaarChar k (gdet h) ^ a * distribHaarChar k ((gdet h)⁻¹ ^ a)) •
            (Measure.addHaar : Measure k).map (fun x => (((gdet h)⁻¹ ^ a : kˣ) : k) * x) := by rw [hcd, one_smul]
      _ = _ := by rw [mul_smul, h2]
  have h1 := GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul k k (Fin a × Fin d) K hu Measure.addHaar inferInstance _ hlam
    (ν.map E) hμ
  simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h1
  have key : ν.map L = (distribHaarChar k (gdet h) ^ a) • ν := by
    apply EM.map_measurableEquiv_injective
    rw [Measure.map_map EM.measurable L.measurable, Measure.map_smul]
    have e1 : (EM ∘ L) = (fun x => K *ᵥ x) ∘ EM := by funext Y; exact (hK Y).symm
    rw [e1, ← Measure.map_map (GlobalTheory.CompanionTheory.SW.DetScale.measurable_mulVec K) EM.measurable]
    exact h1
  have hl := lintegral_map_equiv (fun Y => ‖Φ Y‖ₑ ^ 2) L (μ := ν)
  rw [key] at hl
  refine hl.symm.trans ?_
  rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  congr 1
  simp only [apow, GlobalTheory.SplitWeil.nabs, Complex.cpow_natCast, enorm_pow]
  rw [ENNReal.coe_pow]; congr 1; rw [← ofReal_norm_eq_enorm]; simp

end GlobalTheory.SplitFlip
