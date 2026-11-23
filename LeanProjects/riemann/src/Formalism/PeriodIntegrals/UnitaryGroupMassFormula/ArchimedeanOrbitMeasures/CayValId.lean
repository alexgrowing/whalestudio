import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SumLPresHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PsiInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExpTop

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Metric Filter Formalism.MainNotions.S Formalism.MainNotions.S.Gauge
open scoped ENNReal

namespace CVI

theorem ratio_tendsto {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (g : E → ℝ) (hg : ContinuousAt g 0) :
    Tendsto (fun ρ : ℝ => (∫⁻ p in ball (0 : E) ρ, ENNReal.ofReal (g p) ∂μ).toReal / (μ (ball (0 : E) ρ)).toReal)
      (𝓝[>] 0) (𝓝 (max (g 0) 0)) := by
  set c := max (g 0) 0 with hc
  have hc0 : 0 ≤ c := le_max_right _ _
  have hofr : ∀ p, ENNReal.ofReal (g p) = ENNReal.ofReal (max (g p) 0) := by
    intro p
    rcases le_total (g p) 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
    · rw [max_eq_left h]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.1 hg (ε / 2) (by linarith)
  refine ⟨δ, hδ, fun ρ hρ hρδ => ?_⟩
  have hρ0 : 0 < ρ := hρ
  have hρδ' : ρ < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hρ0] at hρδ
    exact hρδ
  have hbd : ∀ p ∈ ball (0 : E) ρ, |max (g p) 0 - c| < ε / 2 := by
    intro p hp
    have h1 : dist p 0 < δ := lt_trans (mem_ball.1 hp) hρδ'
    have h2 := hδg h1
    rw [Real.dist_eq] at h2
    exact lt_of_le_of_lt (abs_max_sub_max_le_abs _ _ _) h2
  have hBpos : μ (ball (0 : E) ρ) ≠ 0 := (measure_ball_pos μ 0 hρ0).ne'
  have hBfin : μ (ball (0 : E) ρ) ≠ ⊤ := measure_ball_lt_top.ne
  have hBr : 0 < (μ (ball (0 : E) ρ)).toReal := ENNReal.toReal_pos hBpos hBfin
  have hup : ∫⁻ p in ball (0 : E) ρ, ENNReal.ofReal (g p) ∂μ ≤
      ENNReal.ofReal (c + ε / 2) * μ (ball (0 : E) ρ) := by
    rw [← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_ball fun p hp => ?_
    rw [hofr]
    apply ENNReal.ofReal_le_ofReal
    have := hbd p hp
    rw [abs_lt] at this
    linarith
  have hlo : ENNReal.ofReal (c - ε / 2) * μ (ball (0 : E) ρ) ≤
      ∫⁻ p in ball (0 : E) ρ, ENNReal.ofReal (g p) ∂μ := by
    rw [← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_ball fun p hp => ?_
    rw [hofr]
    apply ENNReal.ofReal_le_ofReal
    have := hbd p hp
    rw [abs_lt] at this
    linarith
  have hfin : ENNReal.ofReal (c + ε / 2) * μ (ball (0 : E) ρ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin
  have hup' := ENNReal.toReal_mono hfin hup
  have hlo' := ENNReal.toReal_mono (ne_top_of_le_ne_top hfin hup) hlo
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at hup'
  rw [ENNReal.toReal_mul] at hlo'
  have hlo'' : (c - ε / 2) * (μ (ball (0 : E) ρ)).toReal ≤
      (∫⁻ p in ball (0 : E) ρ, ENNReal.ofReal (g p) ∂μ).toReal := by
    refine le_trans ?_ hlo'
    apply mul_le_mul_of_nonneg_right _ hBr.le
    rw [ENNReal.toReal_ofReal']
    exact le_max_left _ _
  have hA1 : c - ε / 2 ≤ (∫⁻ p in ball (0 : E) ρ, ENNReal.ofReal (g p) ∂μ).toReal / (μ (ball (0 : E) ρ)).toReal := by
    rw [le_div_iff₀ hBr]
    exact hlo''
  have hA2 : (∫⁻ p in ball (0 : E) ρ, ENNReal.ofReal (g p) ∂μ).toReal / (μ (ball (0 : E) ρ)).toReal ≤ c + ε / 2 := by
    rw [div_le_iff₀ hBr]
    exact hup'
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem expDens_gen {n : ℕ} (ε : Fin n → Bool) (r₀ : ℝ) (hr₀ : 0 < r₀) (f₀ : gLie ε → ℝ) (hfm : Measurable f₀)
    (hfc : ContinuousAt f₀ 0)
    (hf : ∀ S ⊆ ball (0 : gLie ε) r₀, MeasurableSet S →
        Formalism.REAL.muG ε ((fun x : gLie ε => cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' S) =
          ∫⁻ x in S, ENNReal.ofReal (f₀ x))
    (m h : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))) (hmh : m ⊔ h = gLie ε)
    (horth : ∀ x ∈ m, ∀ y ∈ h, inner ℝ x y = 0)
    (ι η : Type) [Fintype ι] [Fintype η] (L₀ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] m) (L₁ : EuclideanSpace ℝ η ≃ₗᵢ[ℝ] h) :
    ∃ r : ℝ, 0 < r ∧ ∃ D : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ,
      ContinuousAt D 0 ∧ D 0 = f₀ 0 ∧ Measurable D ∧
      ∀ A ⊆ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r, MeasurableSet A →
        Formalism.REAL.muG ε ((fun p => expR ε (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) *
          expR ε (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' A) =
        ∫⁻ p in A, ENNReal.ofReal (D p) := by

  obtain ⟨-, hpres⟩ := sumLPres_holds n ε m h hmh horth ι η L₀ L₁
  set Ls := sumL ε m h hmh L₀ L₁ with hLs
  have hLc : Continuous Ls := Ls.continuous_of_finiteDimensional
  have hL0 : Ls 0 = 0 := map_zero Ls
  have hnorm : ∀ p, ‖Ls p‖ ≤ 2 * ‖p‖ := by
    intro p
    have e : ‖Ls p‖ = ‖(L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) + (L₁ p.2 : _)‖ := rfl
    rw [e]
    calc _ ≤ ‖(L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ + ‖(L₁ p.2 : EuclideanSpace ℝ _)‖ := norm_add_le _ _
      _ = ‖p.1‖ + ‖p.2‖ := by
          have e1 : ‖(L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖p.1‖ := by
            rw [← LinearIsometryEquiv.norm_map L₀ p.1]; rfl
          have e2 : ‖(L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖p.2‖ := by
            rw [← LinearIsometryEquiv.norm_map L₁ p.2]; rfl
          rw [e1, e2]
      _ ≤ ‖p‖ + ‖p‖ := add_le_add (norm_fst_le p) (norm_snd_le p)
      _ = 2 * ‖p‖ := by ring
  have hC : ∀ S ⊆ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) (r₀ / 2), MeasurableSet S →
      Formalism.REAL.muG ε ((fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
        cayR ε ((L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
          (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)))) '' S) = ∫⁻ p in S, ENNReal.ofReal (f₀ (Ls p)) := by
    intro S hS hSm
    obtain ⟨hIm, hint⟩ := hpres S hSm
    have hsub : Ls '' S ⊆ ball (0 : gLie ε) r₀ := by
      rintro _ ⟨q, hq, rfl⟩
      have hq' := hS hq
      rw [mem_ball_zero_iff] at hq' ⊢
      linarith [hnorm q]
    have e : (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η => cayR ε ((L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
        (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)))) '' S =
        (fun x : gLie ε => cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' (Ls '' S) := by
      rw [Set.image_image]; rfl
    rw [e, hf _ hsub hIm]
    exact hint (fun x => ENNReal.ofReal (f₀ x)) (ENNReal.measurable_ofReal.comp hfm)
  have hFc : ContinuousAt (fun p => f₀ (Ls p)) 0 :=
    ContinuousAt.comp (x := 0) (show ContinuousAt f₀ (Ls 0) by rw [hL0]; exact hfc) hLc.continuousAt

  have hHaar : (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have hL : CayLiftU :=
    cayLiftU_of (cayPsiU_of psiSmooth_holds psiMeas_holds (psiInv_of lieSkew_holds skewLie_holds caySkew_holds cayId_holds))
  obtain ⟨U, hU, ψ, ψ', hψ, hinj, hψ0, hψc, hψm, hψ'm, hdc, hd0, heq⟩ := hL n ε m h hmh horth ι η L₀ L₁
  have hr₁ : 0 < r₀ / 2 := by positivity
  have hpre : ψ ⁻¹' ball 0 (r₀ / 2) ∈ 𝓝 (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) :=
    hψc.preimage_mem_nhds (by rw [hψ0]; exact ball_mem_nhds _ hr₁)
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hU hpre)
  refine ⟨r, hr, fun p => |(ψ' p).det| * f₀ (Ls (ψ p)), ?_, ?_, ?_, ?_⟩
  · exact chart_change_cont (fun p => f₀ (Ls p)) ψ ψ' 0 hψc (by rw [hψ0]; exact hFc) hdc
  · simp only; rw [hd0, hψ0, hL0, one_mul]
  · exact (continuous_abs.measurable.comp (ContinuousLinearMap.continuous_det.measurable.comp hψ'm)).mul
      (hfm.comp (hLc.measurable.comp hψm))
  · intro A hA hAm
    have hAU : A ⊆ ball 0 r := hA
    have e : (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
        expR ε (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) *
          expR ε (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' A =
        ((fun p => cayR ε ((L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
          (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)))) ∘ ψ) '' A := by
      refine Set.image_congr fun p hp => ?_
      exact (heq p (hrs (hAU hp)).1).symm
    rw [e]
    exact chart_change volume _ _ (ball 0 (r₀ / 2)) (fun p => f₀ (Ls p)) hC ψ ψ' (ball 0 r)
      (fun p hp => (hψ p (hrs hp).1).mono fun q hq => (hrs hq).1) (hinj.mono fun q hq => (hrs hq).1)
      (by rintro _ ⟨q, hq, rfl⟩; exact (hrs hq).2) A hAU hAm

theorem expR_zero' {n : ℕ} (ε : Fin n → Bool) : expR ε (0 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) = 1 := by
  unfold expR
  split_ifs with h
  · apply Subtype.ext
    apply Units.ext
    simp [unrealify_zero', NormedSpace.exp_zero]
  · rfl

end CVI

open CVI in

theorem cayValId_holds : CayValId := by
  intro n ε hG r₀ hr₀ f₀ hfm hfc hf
  classical
  let L₀ := (stdOrthonormalBasis ℝ (gLie ε)).repr.symm
  let L₁ := (stdOrthonormalBasis ℝ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool)))).repr.symm
  have hmh : gLie ε ⊔ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))) = gLie ε := sup_bot_eq _
  have horth : ∀ x ∈ gLie ε, ∀ y ∈ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))), inner ℝ x y = 0 := by
    intro x _ y hy; rw [(Submodule.mem_bot ℝ).1 hy, inner_zero_right]
  obtain ⟨r, hr, D, hDc, hD0, -, hD⟩ := expDens_gen ε r₀ hr₀ f₀ hfm hfc hf _ _ hmh horth _ _ L₀ L₁
  obtain ⟨-, hpres⟩ := sumLPres_holds n ε _ _ hmh horth _ _ L₀ L₁
  set Ls := sumL ε _ _ hmh L₀ L₁ with hLs
  have hy0 : ∀ y, ((L₁ y : (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool)))) :
      EuclideanSpace ℝ (Fin n × Fin n × Bool)) = 0 := fun y => (Submodule.mem_bot ℝ).1 (L₁ y).2
  have hyz : ∀ y : EuclideanSpace ℝ (Fin (Module.finrank ℝ ↥(⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))))),
      y = 0 := fun y => by
    have h1 : L₁ y = 0 := Subtype.ext (hy0 y)
    have h2 := congrArg L₁.symm h1
    rwa [LinearIsometryEquiv.symm_apply_apply, map_zero] at h2
  have hLsv : ∀ p, ((Ls p : gLie ε) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) =
      ((L₀ p.1 : gLie ε) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) := fun p => by
    show ((L₀ p.1 : gLie ε) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) + (L₁ p.2 : EuclideanSpace ℝ _) = _
    rw [hy0, add_zero]
  have hnorm : ∀ p, ‖Ls p‖ = ‖p‖ := fun p => by
    have e1 : ‖Ls p‖ = ‖L₀ p.1‖ := by
      show ‖((Ls p : gLie ε) : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ =
        ‖((L₀ p.1 : gLie ε) : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖
      rw [hLsv]
    rw [e1, LinearIsometryEquiv.norm_map, Prod.norm_def, hyz p.2, norm_zero, max_eq_left (norm_nonneg _)]
  have hball : ∀ ρ, Ls '' ball 0 ρ = ball (0 : gLie ε) ρ := fun ρ => by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [mem_ball_zero_iff, hnorm]; exact mem_ball_zero_iff.1 hp
    · intro hx
      refine ⟨(L₀.symm x, 0), ?_, ?_⟩
      · have e : Ls (L₀.symm x, 0) = x := by
          apply Subtype.ext; rw [hLsv]; simp
        rw [mem_ball_zero_iff, ← hnorm, e]; exact mem_ball_zero_iff.1 hx
      · apply Subtype.ext; rw [hLsv]; simp
  have hexp : ∀ ρ, (fun p : EuclideanSpace ℝ (Fin (Module.finrank ℝ (gLie ε))) × EuclideanSpace ℝ (Fin (Module.finrank ℝ ↥(⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))))) =>
      expR ε ((L₀ p.1 : gLie ε) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) *
        expR ε ((L₁ p.2 : (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool)))) :
          EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' ball 0 ρ = expSet ε (ball 0 ρ) := fun ρ => by
    ext g
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨Ls p, by rw [← hball]; exact ⟨p, hp, rfl⟩, ?_⟩
      dsimp only
      rw [hy0, expR_zero', mul_one, hLsv]
      show (((expR ε _ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = _
      exact expR_val ε _ (lieSkew_holds n ε _ (L₀ p.1).2)
    · rintro ⟨x, hx, hgx⟩
      refine ⟨(L₀.symm x, 0), ?_, ?_⟩
      · rw [mem_ball_zero_iff, ← hnorm]
        have e : Ls (L₀.symm x, 0) = x := by
          apply Subtype.ext; rw [hLsv]; simp
        rw [e]; exact mem_ball_zero_iff.1 hx
      · simp only [hy0, expR_zero', mul_one, LinearIsometryEquiv.apply_symm_apply]
        apply Subtype.ext; apply Units.ext
        rw [expR_val ε _ (lieSkew_holds n ε _ x.2)]
        exact hgx.symm
  have hvol : ∀ ρ, volume (ball (0 : gLie ε) ρ) = volume (ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (gLie ε))) × EuclideanSpace ℝ (Fin (Module.finrank ℝ ↥(⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool)))))) ρ) :=
    fun ρ => by
      have := (hpres (ball 0 ρ) measurableSet_ball).2 (fun _ => 1) measurable_const
      rw [hball] at this
      simpa using this
  have hHaar : (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ (gLie ε))) × EuclideanSpace ℝ (Fin (Module.finrank ℝ ↥(⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))))))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have hT := ratio_tendsto (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ (gLie ε))) × EuclideanSpace ℝ (Fin (Module.finrank ℝ ↥(⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))))))) D hDc
  have hlim : Tendsto (ratioAt ε) (𝓝[>] 0) (𝓝 (max (D 0) 0)) := by
    refine hT.congr' (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsGT hr) fun ρ hρ => ?_)
    rw [ratioAt, ← hexp, hD _ (ball_subset_ball hρ.2.le) measurableSet_ball, hvol]
  have hu := tendsto_nhds_unique hG.1 hlim
  rw [hD0] at hu
  rcases le_total (f₀ 0) 0 with h | h
  · rw [max_eq_right h] at hu; linarith [hG.2]
  · rw [max_eq_left h] at hu; exact hu.symm

end PI.AprimeInfW
