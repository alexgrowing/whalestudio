import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationPreservesFlatFormStatement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.FlatTransl

open Filter Topology

variable {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem fderiv_fderiv_I_smul {U : Set (Pt E g)} (hU : IsOpen U) {T : Pt E g → Pt E g}
    (hTd : DifferentiableOn ℂ T U) {P : Pt E g} (hP : P ∈ U)
    (hD : DifferentiableAt ℝ (fderiv ℝ T) P) (w c : Pt E g) :
    fderiv ℝ (fderiv ℝ T) P w (Complex.I • c) = Complex.I • fderiv ℝ (fderiv ℝ T) P w c := by
  have hev : (fun Q => fderiv ℝ T Q (Complex.I • c)) =ᶠ[𝓝 P]
      fun Q => Complex.I • fderiv ℝ T Q c := by
    filter_upwards [hU.mem_nhds hP] with Q hQ
    have hQd : DifferentiableAt ℂ T Q := (hTd Q hQ).differentiableAt (hU.mem_nhds hQ)
    rw [hQd.fderiv_restrictScalars ℝ]
    simp
  have h1 : HasFDerivAt (fun Q => fderiv ℝ T Q (Complex.I • c))
      ((fderiv ℝ (fderiv ℝ T) P).flip (Complex.I • c)) P := by
    simpa using hD.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • c) P)
  have h2 : HasFDerivAt (fun Q => Complex.I • fderiv ℝ T Q c)
      (Complex.I • (fderiv ℝ (fderiv ℝ T) P).flip c) P := by
    have := hD.hasFDerivAt.clm_apply (hasFDerivAt_const c P)
    simp only [ContinuousLinearMap.comp_zero, zero_add] at this
    exact this.const_smul Complex.I
  have := (h1.congr_of_eventuallyEq hev.symm).unique h2
  simpa using congrArg (fun L => L w) this

theorem ddc_comp {U : Set (Pt E g)} (hU : IsOpen U) {T : Pt E g → Pt E g}
    (hTd : DifferentiableOn ℂ T U) (hTs : ContDiffOn ℝ 2 T U) (hTU : Set.MapsTo T U U)
    {u : Pt E g → ℝ} (hu : ContDiffOn ℝ 2 u U) {P : Pt E g} (hP : P ∈ U) (v w : Pt E g) :
    ddc (u ∘ T) P v w = ddc u (T P) (fderiv ℝ T P v) (fderiv ℝ T P w) := by
  have hTP : T P ∈ U := hTU hP
  have hTat : ContDiffAt ℝ 2 T P := hTs.contDiffAt (hU.mem_nhds hP)
  have huat : ContDiffAt ℝ 2 u (T P) := hu.contDiffAt (hU.mem_nhds hTP)
  have hDT : DifferentiableAt ℝ (fderiv ℝ T) P :=
    (hTat.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDU : DifferentiableAt ℝ (fderiv ℝ u) (T P) :=
    (huat.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hT1 : HasFDerivAt T (fderiv ℝ T P) P := (hTat.differentiableAt (by norm_num)).hasFDerivAt

  have hev : ∀ c, (fun Q => fderiv ℝ (u ∘ T) Q c) =ᶠ[𝓝 P]
      fun Q => fderiv ℝ u (T Q) (fderiv ℝ T Q c) := by
    intro c
    filter_upwards [hU.mem_nhds hP] with Q hQ
    have hTQ : DifferentiableAt ℝ T Q :=
      ((hTd Q hQ).differentiableAt (hU.mem_nhds hQ)).restrictScalars ℝ
    have huQ : DifferentiableAt ℝ u (T Q) :=
      (hu.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds (hTU hQ))
    rw [fderiv_comp Q huQ hTQ]
    rfl
  have hA : HasFDerivAt (fun Q => fderiv ℝ u (T Q))
      ((fderiv ℝ (fderiv ℝ u) (T P)).comp (fderiv ℝ T P)) P := hDU.hasFDerivAt.comp P hT1
  have hB : ∀ c, HasFDerivAt (fun Q => fderiv ℝ T Q c)
      ((fderiv ℝ (fderiv ℝ T) P).flip c) P := fun c => by
    simpa using hDT.hasFDerivAt.clm_apply (hasFDerivAt_const c P)
  have hphi : ∀ c x, fderiv ℝ (fun Q => fderiv ℝ (u ∘ T) Q c) P x =
      fderiv ℝ u (T P) (fderiv ℝ (fderiv ℝ T) P x c) +
        fderiv ℝ (fderiv ℝ u) (T P) (fderiv ℝ T P x) (fderiv ℝ T P c) := by
    intro c x
    rw [(hev c).fderiv_eq, (hA.clm_apply (hB c)).fderiv]
    simp
  have hpsi : ∀ c x, fderiv ℝ (fun Q => fderiv ℝ u Q c) (T P) x =
      fderiv ℝ (fderiv ℝ u) (T P) x c := by
    intro c x
    rw [(hDU.hasFDerivAt.clm_apply (hasFDerivAt_const c (T P))).fderiv]
    simp
  have hhol : ∀ c, fderiv ℝ T P (Complex.I • c) = Complex.I • fderiv ℝ T P c := by
    intro c
    rw [((hTd P hP).differentiableAt (hU.mem_nhds hP)).fderiv_restrictScalars ℝ]
    simp
  have hsym := hTat.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have key : fderiv ℝ (fderiv ℝ T) P w (Complex.I • v) =
      fderiv ℝ (fderiv ℝ T) P v (Complex.I • w) := by
    rw [fderiv_fderiv_I_smul hU hTd hP hDT, fderiv_fderiv_I_smul hU hTd hP hDT, hsym w v]
  unfold ddc
  rw [hphi, hphi, hpsi, hpsi, key, ← hhol, ← hhol]
  ring

end GlobalTheory.FlatTransl

namespace GlobalTheory.FlatTransl

theorem translate_isMetric_chernIsFlat : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ},
    IsPeriodMap B τ → ∀ (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ) (h : Pt E g → ℝ),
    IsMetric B τ M j h → ChernIsFlat B τ h → ∀ x : Fl g,
    IsMetric B τ M (translPullFactor τ x j) (fun P => h (transl τ x P)) ∧
      ChernIsFlat B τ (fun P => h (transl τ x P)) := by
  intro g E _ _ _ B τ hτ M j h hM hC x
  obtain ⟨hTd, hpull⟩ := GlobalTheory.T.translation_preserves_flat_form hτ x
  have hU : IsOpen (cov B g) := hτ.1.prod isOpen_univ
  have hmaps : Set.MapsTo (transl τ x) (cov B g) (cov B g) := fun P hP => ⟨hP.1, trivial⟩
  have hTs : ContDiffOn ℝ ∞ (transl τ x) (cov B g) :=
    (GlobalTheory.SCV.contDiffOn_of_differentiableOn hU hTd ∞).restrict_scalars ℝ
  refine ⟨⟨hM.1.comp hTs hmaps, fun P hP => hM.2.1 _ (hmaps hP), fun l hl P hP => ?_⟩,
    fun P hP v w => ?_⟩
  · have hc : transl τ x (transl τ l P) = transl τ l (transl τ x P) :=
      Prod.ext rfl (add_right_comm _ _ _)
    simp only [translPullFactor]
    rw [hc]
    exact hM.2.2 l hl _ (hmaps hP)
  · have hu : ContDiffOn ℝ 2 (fun Q => Real.log (h Q)) (cov B g) :=
      (hM.1.log fun Q hQ => (hM.2.1 Q hQ).ne').of_le (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.2 le_top)
    have e := ddc_comp hU hTd (hTs.of_le (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.2 le_top)) hmaps hu hP v w
    change -ddc ((fun Q => Real.log (h Q)) ∘ transl τ x) P v w = _
    rw [e, hC _ (hmaps hP), ← hpull P hP]
    simp only [pull, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    fin_cases i <;> rfl

end GlobalTheory.FlatTransl
