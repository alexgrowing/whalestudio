import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.ThmFD
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdegTransfer
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RangeDatumEmbedding
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.EquivSigLamOfIsDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsDSSigLam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.IsDSSigLam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.Imports
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.PsiFor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.ImportsAlt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.StdGapOfGapLap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PsiMExpPmat
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdc_big {ε : Fin n → Bool} {h : ℝ} (hh : thrS ε + 1 < h) :
    2 * (n : ℝ) < h := by
  unfold thrS at hh
  have h1 := le_max_left (2 * (n : ℝ))
    (16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)))
  linarith

theorem one_le_q0_of_p_q_pos {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) : 1 ≤ S7.q0 ε := by
  show 1 ≤ min (pOf ε) (qOf ε)
  exact le_min hp hq

theorem fdc_eight {ε : Fin n → Bool} {h : ℝ} (hh : thrS ε + 1 < h) :
    8 * (n : ℝ) * (S7.q0 ε : ℝ) < h := by
  unfold thrS at hh
  have h1 := le_max_right (2 * (n : ℝ))
    (16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)))
  have h2 : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ) := by positivity
  have h3 : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
  nlinarith

theorem fdc_stdGap {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h)
    (hh : thrS ε + 1 < h) : StdGap ε μ :=
  ⟨hμ.1, h, hg, fdc_big hh⟩

theorem fdc_hc_add {μ : Fin n → ℝ} {s : Fin n} (hμ : IsHCParam μ) (hs : StrictAnti (μ + Pi.single s 1)) :
    IsHCParam (μ + Pi.single s 1) := by
  refine ⟨hs, fun a => ?_⟩
  obtain ⟨m, hm⟩ := hμ.2 a
  by_cases has : a = s
  · subst has
    refine ⟨m + 1, ?_⟩
    rw [Pi.add_apply, Pi.single_eq_same]
    push_cast
    linarith
  · refine ⟨m, ?_⟩
    rw [Pi.add_apply, Pi.single_eq_of_ne has, add_zero]
    exact hm

theorem fdc_w_ne {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : T.w ≠ 0 := by
  letI := T.instNACG
  intro h
  have h1 := T.w_norm
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem fdc_model {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {μ : Fin n → ℝ} {h : ℝ}
    (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h) (hh : thrS ε + 1 < h) (T : KType ε (lowK ε μ)) :
    ∃ m : Fin n → ℤ, IsMu μ m ∧ IsPsiFor ε μ T (PsiM T m) := by
  obtain ⟨m, hm⟩ := Lap.LemK.exists_isMu hμ
  exact ⟨m, hm, (Lap.Base.psiFor n ε μ h T m hμ hm hg (one_le_q0_of_p_q_pos hp hq) (fdc_eight hh)).1⟩

abbrev FdcGood (ε : Fin n → Bool) (μ : Fin n → ℝ) (d : ℝ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε μ σ ∧ Formalism.MainNotions.S.IsFdeg (muCD ε) σ d

def fdcD (ε : Fin n → Bool) (μ : Fin n → ℝ) : ℝ := by
  classical
  exact if h : ∃ d, FdcGood ε μ d then h.choose else 0

theorem fdc_fdegOf_eq {ε : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')} (U : H ≃ₗᵢ[ℂ] H')
    (hU : ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ x : H, U (σ g x) = σ' g (U x)) (ν : Measure (Formalism.REAL.UJ ε)) (v : H) :
    Formalism.MainNotions.S.fdegOf ν σ' (U v) = Formalism.MainNotions.S.fdegOf ν σ v := by
  have hfun : (fun g : Formalism.REAL.UJ ε => ‖⟪U v, σ' (Formalism.MainNotions.S.umat g) (U v)⟫_ℂ‖ ^ 2) =
      fun g => ‖⟪v, σ (Formalism.MainNotions.S.umat g) v⟫_ℂ‖ ^ 2 := by
    funext g
    rw [← hU (Formalism.MainNotions.S.umat g) g.2 v, LinearIsometryEquiv.inner_map_map]
  simp only [Formalism.MainNotions.S.fdegOf, Formalism.MainNotions.S.coefOn]
  rw [LinearIsometryEquiv.norm_map, hfun]

theorem fdcGood_unique {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h)
    (hh : thrS ε + 1 < h) {d d' : ℝ} (h1 : FdcGood ε μ d) (h2 : FdcGood ε μ d') : d = d' := by
  obtain ⟨H, _, _, σ, hσ, hd⟩ := h1
  obtain ⟨H', _, _, σ', hσ', hd'⟩ := h2
  have := hσ.1
  have := hσ'.1
  have := hσ.2.1
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  obtain ⟨U, hU⟩ := (isDS_props_of_gap n ε μ hμ h hg (fdc_big hh) H σ hσ).2.2.2.2 H' σ' hσ'
  have hUv : U v ≠ 0 := by simpa using hv
  rw [← fdegOf_of_isFdeg' hd hv, ← fdegOf_of_isFdeg' hd' hUv, fdc_fdegOf_eq U hU]

theorem fdcD_eq {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h)
    (hh : thrS ε + 1 < h) {d : ℝ} (hd : FdcGood ε μ d) : fdcD ε μ = d := by
  have hex : ∃ d, FdcGood ε μ d := ⟨d, hd⟩
  rw [fdcD, dif_pos hex]
  exact fdcGood_unique hμ hg hh hex.choose_spec hd

theorem fdcGood_of_isDS {ε : Fin n → Bool} {μ : Fin n → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsDS ε μ σ) :
    ∃ d, Formalism.MainNotions.S.IsFdeg (muCD ε) σ d := by
  have := hσ.1
  obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS μ σ hσ
  exact isFdeg_muCD hd

theorem fdc_ds_exists {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {μ : Fin n → ℝ} {h : ℝ}
    (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h) (hh : thrS ε + 1 < h) : ∃ d, FdcGood ε μ d := by
  obtain ⟨T⟩ := HW.kType_exists ε μ hμ
  obtain ⟨m, -, hP⟩ := fdc_model hp hq hμ hg hh T
  have hDS := isDS_sigLam (fdc_stdGap hμ hg hh) hP (fdc_w_ne T)
  obtain ⟨d, hd⟩ := fdcGood_of_isDS hDS
  exact ⟨d, _, inferInstance, inferInstance, _, hDS, hd⟩

theorem fdc_step {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {h : ℝ} (hh : thrS ε + 1 < h) :
    ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h →
      GapAtLeast ε (μ + Pi.single s 1) h → StrictAnti (μ + Pi.single s 1) →
        fdcD ε (μ + Pi.single s 1) = fdcD ε μ * ratioV μ s := by
  intro μ s hμ hg hg' hs
  have hμ' : IsHCParam (μ + Pi.single s 1) := fdc_hc_add hμ hs
  obtain ⟨d, H, _, _, σ, hσ, hd⟩ := fdc_ds_exists hp hq hμ hg hh
  obtain ⟨d', H', _, _, σ', hσ', -⟩ := fdc_ds_exists hp hq hμ' hg' hh
  have hr := fdeg_ratio_V hp hq hμ hg hh s hs hσ hσ' (muCD ε) (muCD_isHaar ε) hd
  rw [fdcD_eq hμ hg hh ⟨H, inferInstance, inferInstance, σ, hσ, hd⟩,
    fdcD_eq hμ' hg' hh ⟨H', inferInstance, inferInstance, σ', hσ', hr⟩]

end ReciprocityTheory.ChartRestriction.DS.G2
