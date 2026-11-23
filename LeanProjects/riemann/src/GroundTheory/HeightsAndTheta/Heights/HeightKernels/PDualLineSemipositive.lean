import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStC
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix NumberField
open scoped ComplexOrder

noncomputable section

namespace DualLineSemipositiveAlt

open scoped MatrixOrder in

theorem exists_conjTranspose_mul_self {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (hM : M.PosSemidef) : ∃ B : Matrix n n ℂ, M = Bᴴ * B := by
  have h0 : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM
  refine ⟨CFC.sqrt M, ?_⟩
  rw [← Matrix.star_eq_conjTranspose, (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq,
    CFC.sqrt_mul_sqrt_self M h0]

theorem re_star_dotProduct_mulVec {n : Type} [Fintype n] (B : Matrix n n ℂ) (w : n → ℂ) :
    (star w ⬝ᵥ ((Bᴴ * B) *ᵥ w)).re = ∑ j, ‖(B *ᵥ w) j‖ ^ 2 := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

def factor (F : HermLattice K i) (σ : K →+* ℂ) : Matrix (Fin i) (Fin i) ℂ :=
  Classical.choose (exists_conjTranspose_mul_self (F.posDef σ).posSemidef)

theorem factor_spec (F : HermLattice K i) (σ : K →+* ℂ) :
    F.metric σ = (factor F σ)ᴴ * factor F σ :=
  Classical.choose_spec (exists_conjTranspose_mul_self (F.posDef σ).posSemidef)

def coordMap {F : HermLattice K i} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    ((Σ _ : Unit, T) → ℂ) →ₗ[ℂ] ((K →+* ℂ) × Fin i → ℂ) :=
  (LinearMap.pi fun p : (K →+* ℂ) × Fin i => (LinearMap.proj p.2) ∘ₗ (factor F p.1).mulVecLin ∘ₗ
      (LinearMap.pi fun k => LinearMap.proj (p.1, k))) ∘ₗ (dualRecover b hb).toLinearMap ∘ₗ
    (LinearMap.pi fun t => LinearMap.proj (⟨(), t⟩ : Σ _ : Unit, T))

omit [Fintype T] [DecidableEq T] in

theorem dualLine_h_eq {F : HermLattice K i} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : (Σ _ : Unit, T) → ℂ) :
    (dualLine F b hb).h z = (fsMetric ((K →+* ℂ) × Fin i)).ρ (coordMap b hb z) := by
  show Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩) = ‖WithLp.toLp 2 (coordMap b hb z)‖
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp only [dualNormSq]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [factor_spec F σ, re_star_dotProduct_mulVec]
  rfl

end DualLineSemipositiveAlt

open DualLineSemipositiveAlt in

theorem DualLineSemipositive.proof : DualLineSemipositive.Statement := by
  intro K _ _ i F T _ _ b hb
  set τc : ((Σ _ : Unit, T) → ℂ) →L[ℂ] ((K →+* ℂ) × Fin i → ℂ) :=
    LinearMap.toContinuousLinearMap (coordMap b hb) with hτc
  have hh : ∀ z, (dualLine F b hb).h z = (fsMetric ((K →+* ℂ) × Fin i)).ρ (τc z) :=
    dualLine_h_eq b hb
  have hne : ∀ z : (Σ _ : Unit, T) → ℂ, (∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) → τc z ≠ 0 := by
    intro z hz h0
    have hp := (dualLine F b hb).pos z hz
    rw [hh, h0] at hp
    simp [fsMetric] at hp
  have hfun : (dualLine F b hb).h = (fsMetric ((K →+* ℂ) × Fin i)).ρ ∘ τc := funext hh
  refine ⟨?_, fun z hz w _ => ?_⟩
  · intro z hz
    rw [hfun]
    exact ((HilbertSamuel.ProjLine.isSmoothMetric_fs.contDiffAt (isOpen_ne.mem_nhds (hne z hz))).comp z
      (τc.restrictScalars ℝ).contDiff.contDiffAt).contDiffWithinAt
  · change 0 ≤ ReciprocityTheory.AnForm.levi (fun z => Real.log ((dualLine F b hb).h z)) z w
    have hlog : (fun z => Real.log ((dualLine F b hb).h z)) =
        (fun u => Real.log ((fsMetric ((K →+* ℂ) × Fin i)).ρ u)) ∘ τc := by
      funext y
      simp only [Function.comp_apply, hh]
    rw [hlog, ReciprocityTheory.AnForm.levi_comp w (τc.analyticAt z)
      (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_contDiffAt_logρ_id HilbertSamuel.ProjLine.isSmoothMetric_fs
        (hne z hz.1))]
    exact HilbertSamuel.ProjLine.leviForm_log_fs_nonneg (hne z hz.1) _

end

end GroundTheory.Heights₂.Heights
