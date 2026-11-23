import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.FrameDer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeStructureStatement

noncomputable section

open MeasureTheory Matrix Finset Filter
open scoped ContDiff ComplexConjugate Topology ComplexOrder

namespace PositivityTheory.RgBcC.LfSt.UnitaryConjTransposeTrace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contOn_inv : ContinuousOn (fun y : Mat n => y⁻¹) (GLs n) := by
  have h : ∀ y ∈ GLs n, y⁻¹ = (y.det)⁻¹ • y.adjugate := fun y _ => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  refine ContinuousOn.congr ?_ h
  exact ContinuousOn.smul ((continuous_id.matrix_det).continuousOn.inv₀ fun y hy => hy)
    (continuous_id.matrix_adjugate).continuousOn

theorem mem_GLs_mul {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem inv_mem_GLs {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n :=
  (Matrix.isUnit_nonsing_inv_det x (isUnit_iff_ne_zero.2 hx)).ne_zero

theorem conjTranspose_mem_GLs {x : Mat n} (hx : x ∈ GLs n) : xᴴ ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_conjTranspose, star_ne_zero] at *
  exact hx

theorem tw_mem {x d : Mat n} (hx : x ∈ GLs n) (hd : d ∈ GLs n) : x⁻¹ * d * xᴴ⁻¹ ∈ GLs n :=
  mem_GLs_mul (mem_GLs_mul (inv_mem_GLs hx) hd) (inv_mem_GLs (conjTranspose_mem_GLs hx))

theorem val_mem (x : G n) : (x : Mat n) ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit x)).ne_zero

theorem tw_val (x d : G n) : ((tw x d : G n) : Mat n) = (x : Mat n)⁻¹ * d * (x : Mat n)ᴴ⁻¹ := by
  simp only [tw, th, Units.val_mul, Matrix.coe_units_inv, Units.coe_star, Matrix.star_eq_conjTranspose]

def trL (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] : (V →L[ℂ] V) →ₗ[ℂ] ℂ :=
  (LinearMap.trace ℂ V).comp (ContinuousLinearMap.coeLM ℂ)

theorem trL_apply {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (A : V →L[ℂ] V) :
    trL V A = LinearMap.trace ℂ V (A : V →ₗ[ℂ] V) := rfl

theorem trL_cont (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] : Continuous (trL V) :=
  LinearMap.continuous_of_finiteDimensional _

theorem trL_mul_comm {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (A B : V →L[ℂ] V) : trL V (A * B) = trL V (B * A) := by
  simp only [trL_apply, ContinuousLinearMap.toLinearMap_mul]
  exact LinearMap.trace_mul_comm ℂ _ _

theorem sigma_mem {σ : (Fin n × Fin n → ℝ) → Mat n} (hσ2 : ∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) {v} (hv : v ∈ cone n) :
    σ v ∈ GLs n := by
  have h1 : (hOf v).det ≠ 0 := (show (hOf v).PosDef from hv).det_pos.ne'
  rw [← hσ2 v hv, Matrix.det_mul] at h1
  exact left_ne_zero_of_mul h1

theorem end1 : End1 := by
  intro n lam E Fr ε ι S Γ T hCx _ _ μ _ σ c hσ hσ2 hform k hk hkeq hkΓ d R hR
  set Fm : Mat n → ℂ := fun y => trL E.V (k (y⁻¹ * d.val * yᴴ⁻¹) * T) with hFm
  have hdG := val_mem d
  have harg : ContinuousOn (fun y : Mat n => y⁻¹ * d.val * yᴴ⁻¹) (GLs n) :=
    (contOn_inv.mul continuousOn_const).mul
      (contOn_inv.comp (continuous_id.matrix_conjTranspose).continuousOn fun y hy => conjTranspose_mem_GLs hy)
  have hFmcont : ContinuousOn Fm (GLs n) :=
    (trL_cont E.V).comp_continuousOn ((hk.comp harg fun y hy => tw_mem hy hdG).mul continuousOn_const)
  have hFmsupp : ∃ R, ∀ y ∈ GLs n, R < lg y → Fm y = 0 :=
    ⟨R, fun y hy h => by simp only [hFm, hR y hy h, zero_mul, map_zero]⟩
  have hFmK : ∀ y ∈ GLs n, ∀ kk : Matrix.unitaryGroup (Fin n) ℂ, Fm (y * kk.1) = Fm y := by
    intro y hy kk
    have hu : kk.1ᴴ * kk.1 = 1 := Matrix.UnitaryGroup.star_mul_self kk
    have hu' : kk.1 * kk.1ᴴ = 1 := by
      have := Matrix.mem_unitaryGroup_iff.mp kk.2
      simpa [Matrix.star_eq_conjTranspose] using this
    have hinv : kk.1⁻¹ = kk.1ᴴ := Matrix.inv_eq_left_inv hu
    have hinvH : kk.1ᴴ⁻¹ = kk.1 := Matrix.inv_eq_left_inv hu'
    have e : (y * kk.1)⁻¹ * d.val * (y * kk.1)ᴴ⁻¹ = (kk⁻¹ : Matrix.unitaryGroup (Fin n) ℂ).1 * (y⁻¹ * d.val * yᴴ⁻¹) * kk.1 := by
      rw [Matrix.mul_inv_rev, Matrix.conjTranspose_mul, Matrix.mul_inv_rev, hinvH, hinv]
      have : (kk⁻¹ : Matrix.unitaryGroup (Fin n) ℂ).1 = kk.1ᴴ := by
        rw [Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose]
      rw [this]
      simp only [Matrix.mul_assoc]
    simp only [hFm]
    rw [e, hkeq _ (tw_mem hy hdG)]
    rw [show E.ρ kk⁻¹ * k (y⁻¹ * d.val * yᴴ⁻¹) * E.ρ kk * T = E.ρ kk⁻¹ * (k (y⁻¹ * d.val * yᴴ⁻¹) * T) * E.ρ kk by
      rw [mul_assoc (E.ρ kk⁻¹ * k _) (E.ρ kk) T, ← hCx.TK kk]; simp only [mul_assoc]]
    rw [trL_mul_comm, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hcone : ∀ v ∈ cone n, trL E.V (Γ * S 1 * Kc σ c Fr k Γ T d.val (v, v)) =
      ((c : ℂ) * ((hOf v).det ^ n)⁻¹) * Fm (σ v) := by
    intro v hv
    have hx := sigma_mem hσ2 hv
    simp only [Kc, Kf, hCx.S1, mul_one, mul_smul_comm, map_smul, smul_eq_mul, hFm]
    congr 1
    have hw := tw_mem hx hdG
    have h1 : Fr (σ v)⁻¹ * Fr (σ v) = 1 := by
      rw [← hCx.mul _ (inv_mem_GLs hx) _ hx, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hx), hCx.one]
    calc trL E.V (Γ * (Fr (σ v) * k ((σ v)⁻¹ * d.val * (σ v)ᴴ⁻¹) * Γ * T * Fr (σ v)⁻¹))
        = trL E.V (Fr (σ v) * (Γ * k ((σ v)⁻¹ * d.val * (σ v)ᴴ⁻¹) * Γ * T * Fr (σ v)⁻¹)) := by
          rw [show Γ * (Fr (σ v) * k ((σ v)⁻¹ * d.val * (σ v)ᴴ⁻¹) * Γ * T * Fr (σ v)⁻¹) =
              (Γ * Fr (σ v)) * (k ((σ v)⁻¹ * d.val * (σ v)ᴴ⁻¹) * Γ * T * Fr (σ v)⁻¹) by simp only [mul_assoc],
            hCx.ΓFr _ hx]
          simp only [mul_assoc]
      _ = trL E.V ((Γ * k ((σ v)⁻¹ * d.val * (σ v)ᴴ⁻¹) * Γ * T * Fr (σ v)⁻¹) * Fr (σ v)) := trL_mul_comm _ _
      _ = trL E.V (k ((σ v)⁻¹ * d.val * (σ v)ᴴ⁻¹) * T) := by
          rw [mul_assoc _ (Fr (σ v)⁻¹), h1, mul_one, hkΓ _ hw, mul_assoc (k _) Γ Γ, hCx.Γsq, mul_one]
  have hcontTw : Continuous (fun x : G n => (x : Mat n)⁻¹ * d.val * (x : Mat n)ᴴ⁻¹) :=
    ((contOn_inv.comp_continuous Units.continuous_val val_mem).mul continuous_const).mul
      (contOn_inv.comp_continuous (Units.continuous_val.matrix_conjTranspose) fun x => conjTranspose_mem_GLs (val_mem x))
  have hphi : (fun x : G n => phiOf E T k (tw x d)) = fun x : G n => Fm (x : Mat n) := by
    funext x
    simp only [phiOf, hFm, trL_apply, tw_val]
  have hcont : Continuous (fun x : G n => Fm (x : Mat n)) :=
    (trL_cont E.V).comp ((hk.comp_continuous hcontTw fun x => tw_mem (val_mem x) hdG).mul continuous_const)
  have hcs : HasCompactSupport (fun x : G n => Fm (x : Mat n)) := by
    refine HasCompactSupport.intro (GlobalTheory.T.length_function_compact n R) fun x hx => ?_
    simp only [Set.mem_ofPred_eq, not_le] at hx
    simp only [hFm, hR _ (val_mem x) hx, zero_mul, map_zero]
  refine ⟨hphi ▸ hcont.integrable_of_hasCompactSupport hcs, ?_⟩
  rw [hphi, hform Fm hFmcont hFmsupp hFmK, ← integral_const_mul]
  refine setIntegral_congr_fun (GlobalTheory.T.positive_cone_structure n).1.measurableSet (fun v hv => ?_)
  rw [show Γ * S 1 * Kc σ c Fr k Γ T d.val (v, v) = Γ * S 1 * Kc σ c Fr k Γ T d.val (v, v) from rfl]
  have := hcone v hv
  simp only [trL_apply] at this
  rw [this]; ring

end PositivityTheory.RgBcC.LfSt.UnitaryConjTransposeTrace
