import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StRefChartDisc
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffMulOfTsupport
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open ReciprocityTheory.AnForm.M (IsCompatChart FinHolAtlas)

theorem RefChartDisc.log_norm_eq_re {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (h0 : F 0 ≠ 0) :
    ∃ L : ℂ → ℂ, AnalyticAt ℂ L 0 ∧ ∀ᶠ s in 𝓝 (0 : ℂ), Real.log ‖F s‖ = (L s).re := by
  refine ⟨fun s => Complex.log (F s / F 0) + (Real.log ‖F 0‖ : ℂ), ?_, ?_⟩
  · refine ((hF.div analyticAt_const h0).clog ?_).add analyticAt_const
    show F 0 / F 0 ∈ Complex.slitPlane
    rw [div_self h0]
    exact Complex.one_mem_slitPlane
  · filter_upwards [hF.continuousAt.eventually_ne h0] with s hs
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr hs) (norm_ne_zero_iff.mpr h0)]
    ring

theorem RefChartDisc.analyticAt_comp {n : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas n X}
    {e : OpenPartialHomeomorph X (Fin n → ℂ)} (he : IsCompatChart A e) {y : ℂ → X}
    (hy : AnalyticAt ℂ (fun s => e (y s)) 0) (hys : ∀ᶠ s in 𝓝 (0 : ℂ), y s ∈ e.source)
    {V : Set X} {F : X → ℂ} (hF : A.HoloOn V F) (h0 : y 0 ∈ V) :
    AnalyticAt ℂ (fun s => F (y s)) 0 := by
  have h0s : y 0 ∈ e.source := hys.self_of_nhds
  have h1 : AnalyticAt ℂ (F ∘ e.symm) (e (y 0)) :=
    ReciprocityTheory.AnForm.M.PLAux.analyticAt_compat_fun he hF (e.map_source h0s) (by rwa [e.left_inv h0s])
  refine (h1.comp (f := fun s => e (y s)) hy).congr ?_
  filter_upwards [hys] with s hs
  simp [Function.comp, e.left_inv hs]

theorem RefChartDisc.proof (hProj : ProjChartHolo.Statement) : RefChartDisc.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D H M S j γ hγ hmem hsrc
  set x := M.proj (γ 0) with hx
  set e := S.R.chart j with he_def
  have he : IsCompatChart M.atlas e := S.R.compat j
  have hφ : AnalyticAt ℂ (fun s => e (M.proj (γ s))) 0 := hProj II Ψ K ι Ω E D M e he γ hγ hmem hsrc
  have hγ0 : γ 0 ∈ mcPts (mCoordIdeal D.y) := hmem.self_of_nhds
  have hcont : Tendsto (fun s => M.proj (γ s)) (𝓝 0) (𝓝 x) :=
    (M.cont _ hγ0).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hγ.continuousAt.tendsto, hmem⟩)
  obtain ⟨U, hUo, hxU, hUsub, σ, hσ, hσh, G1, hG1, hG1eq⟩ := S.th_ref x x (S.R.th.mem_U x)
  obtain ⟨W, hWo, hxW, G2, hG2, hG2eq⟩ := S.R.q_th j x x ⟨S.R.th.mem_U x, hsrc⟩
  have hV : ∀ᶠ s in 𝓝 (0 : ℂ), M.proj (γ s) ∈ U ∩ W ∩ e.source :=
    hcont.eventually (((hUo.inter hWo).inter e.open_source).mem_nhds ⟨⟨hxU, hxW⟩, hsrc⟩)
  have hA : ∀ {V : Set M.Xc} {F : M.Xc → ℂ}, M.atlas.HoloOn V F → x ∈ V →
      AnalyticAt ℂ (fun s => F (M.proj (γ s))) 0 :=
    fun hF hxV => RefChartDisc.analyticAt_comp he hφ (hV.mono fun _ h => h.2) hF hxV

  choose i hi using (hσ x hxU).1.1
  set T : K → ℂ → ℂ := fun b s => γ s ⟨b, i b⟩ / σ (M.proj (γ s)) ⟨b, i b⟩ with hT_def
  have hden : ∀ b, AnalyticAt ℂ (fun s => σ (M.proj (γ s)) ⟨b, i b⟩) 0 := fun b => hA (hσh ⟨b, i b⟩) hxU
  have hT : ∀ b, AnalyticAt ℂ (T b) 0 := fun b =>
    (analyticAt_pi_iff.1 hγ ⟨b, i b⟩).div (hden b) (hi b)
  obtain ⟨c0, hc0, hγc0⟩ := (M.fibre _ (hσ x hxU).1 _ hγ0).1 (hσ x hxU).2
  have hT0 : ∀ b, T b 0 ≠ 0 := fun b => by
    have : γ 0 ⟨b, i b⟩ = c0 b * σ x ⟨b, i b⟩ := by rw [hγc0]; rfl
    simp only [hT_def, ← hx, this]
    exact div_ne_zero (mul_ne_zero (hc0 b) (hi b)) (hi b)
  choose L hL hLeq using fun b => RefChartDisc.log_norm_eq_re (hT b) (hT0 b)
  have hdenev : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ b, σ (M.proj (γ s)) ⟨b, i b⟩ ≠ 0 :=
    eventually_all.2 fun b => (hden b).continuousAt.eventually_ne (hi b)
  refine ⟨fun s => G1 (M.proj (γ s)) + G2 (M.proj (γ s)) - ∑ b, ((S.ref.a b : ℝ) : ℂ) * L b s, ?_, ?_⟩
  · refine ((hA hG1 hxU).add (hA hG2 hxW)).sub ?_
    have := Finset.analyticAt_sum (𝕜 := ℂ) Finset.univ fun b _ => (analyticAt_const (v := ((S.ref.a b : ℝ) : ℂ))).mul (hL b)
    refine this.congr (Eventually.of_forall fun s => ?_)
    simp [Finset.sum_apply]
  filter_upwards [hV, hmem, hdenev, eventually_all.2 hLeq] with s hs hγs hds hLs
  obtain ⟨⟨hsU, hsW⟩, hssrc⟩ := hs
  set y := M.proj (γ s) with hy
  obtain ⟨hσy, hpσy⟩ := hσ y hsU
  obtain ⟨c, hc, hγc⟩ := (M.fibre _ hσy _ hγs).1 (by rw [hpσy])
  have hcT : ∀ b, c b = T b s := fun b => by
    have : γ s ⟨b, i b⟩ = c b * σ y ⟨b, i b⟩ := by rw [hγc]; rfl
    simp only [hT_def, ← hy, this]
    field_simp [hds b]
  have hmet : S.ref.h (γ s) = (∏ b, ‖c b‖ ^ S.ref.a b) * S.ref.h (σ y) := by
    rw [← S.ref.smul c (σ y) hc, hγc]; rfl
  have hpos : 0 < S.ref.h (σ y) := S.ref.pos _ hσy.1
  have hlog : Real.log (S.ref.h (γ s)) = ∑ b, (S.ref.a b : ℝ) * (L b s).re + Real.log (S.ref.h (σ y)) := by
    rw [hmet, Real.log_mul (Finset.prod_ne_zero_iff.2 fun b _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc b)))
      hpos.ne', Real.log_prod (fun b _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc b)))]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Real.log_zpow, hcT b, hLs b]
  have h1 := hG1eq y hsU
  have h2 := hG2eq y ⟨⟨hsW, hUsub hsU⟩, hssrc⟩
  simp only [Complex.sub_re, Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul]
  rw [hlog]
  linarith

end GroundTheory.Heights₂.Heights.NineStatements
