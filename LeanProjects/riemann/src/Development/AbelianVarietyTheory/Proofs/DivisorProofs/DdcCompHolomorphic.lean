import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory

theorem ddc_comp_holomorphic {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (U V : Set (Pt E g)) (F : Pt E g → Pt E g) (u : Pt E g → ℝ)
    (hU : IsOpen U) (hV : IsOpen V) (hF : DifferentiableOn ℂ F U) (hFUV : Set.MapsTo F U V)
    (hu : ContDiffOn ℝ 2 u V) : ∀ P ∈ U, ∀ v w : Pt E g,
      ddc (fun Q => u (F Q)) P v w = ddc u (F P) (fderiv ℝ F P v) (fderiv ℝ F P w) := by
  intro P hP v w
  have hFa : AnalyticOnNhd ℂ F U := GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hU hF
  have hFd : ∀ Q ∈ U, DifferentiableAt ℂ F Q := fun Q hQ => hF.differentiableAt (hU.mem_nhds hQ)
  have hFR : ∀ Q ∈ U, fderiv ℝ F Q = (fderiv ℂ F Q).restrictScalars ℝ := fun Q hQ =>
    ((hFd Q hQ).hasFDerivAt.restrictScalars ℝ).fderiv
  have huc : ∀ Q ∈ V, ContDiffAt ℝ 2 u Q := fun Q hQ => hu.contDiffAt (hV.mem_nhds hQ)
  have hFP : ContDiffAt ℂ ω F P := (hFa P hP).contDiffAt
  have hsym : IsSymmSndFDerivAt ℂ F P := hFP.isSymmSndFDerivAt_of_omega
  have hD2 : DifferentiableAt ℂ (fderiv ℂ F) P :=
    (hFP.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hDu : DifferentiableAt ℝ (fderiv ℝ u) (F P) :=
    ((huc _ (hFUV hP)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hFPR : HasFDerivAt F (fderiv ℝ F P) P :=
    ((hFd P hP).restrictScalars ℝ).hasFDerivAt

  have happ : ∀ (y c z : Pt E g),  DifferentiableAt ℝ (fderiv ℝ u) y →
      fderiv ℝ (fun Q => fderiv ℝ u Q c) y z = fderiv ℝ (fderiv ℝ u) y z c := by
    intro y c z hy
    have := hy.hasFDerivAt.clm_apply (hasFDerivAt_const c y)
    rw [this.fderiv]
    simp
  have key : ∀ a b : Pt E g,
      fderiv ℝ (fun Q => fderiv ℝ (fun Q => u (F Q)) Q (Complex.I • a)) P b =
      fderiv ℝ (fderiv ℝ u) (F P) (fderiv ℝ F P b) (Complex.I • fderiv ℝ F P a) +
      fderiv ℝ u (F P) (Complex.I • fderiv ℂ (fderiv ℂ F) P b a) := by
    intro a b
    have heq : (fun Q => fderiv ℝ (fun Q => u (F Q)) Q (Complex.I • a)) =ᶠ[nhds P]
        fun Q => fderiv ℝ u (F Q) (Complex.I • fderiv ℂ F Q a) := by
      filter_upwards [hU.mem_nhds hP] with Q hQ
      have hd : DifferentiableAt ℝ u (F Q) :=
        (huc _ (hFUV hQ)).differentiableAt (by norm_num)
      rw [fderiv_comp' Q hd ((hFd Q hQ).restrictScalars ℝ), hFR Q hQ]
      simp
    rw [heq.fderiv_eq]
    have hA : HasFDerivAt (fun Q => fderiv ℝ u (F Q))
        ((fderiv ℝ (fderiv ℝ u) (F P)).comp (fderiv ℝ F P)) P :=
      hDu.hasFDerivAt.comp P hFPR
    have hx : HasFDerivAt (fun Q => fderiv ℂ F Q a)
        ((ContinuousLinearMap.apply ℂ (Pt E g) a).comp (fderiv ℂ (fderiv ℂ F) P)) P :=
      (ContinuousLinearMap.apply ℂ (Pt E g) a).hasFDerivAt.comp P hD2.hasFDerivAt
    have hxI := (hx.restrictScalars ℝ).const_smul Complex.I
    have := hA.clm_apply (u := fun Q => Complex.I • fderiv ℂ F Q a) hxI
    rw [this.fderiv]
    simp [hFR P hP]
    ring
  have e1 := key v w
  have e2 := key w v
  have s := hsym v w
  unfold ddc
  rw [e1, e2, happ _ _ _ hDu, happ _ _ _ hDu, hFR P hP]
  simp only [ContinuousLinearMap.coe_restrictScalars', s]
  ring

end GlobalTheory
