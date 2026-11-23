import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem epsT_small (C : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ t, 0 < t → t ≤ a → |epsT C t| ≤ 1 / 2 ∧ C * epsT C t ≤ 1 := by
  have hL : Tendsto (fun t : ℝ => Real.log (1 / t)) (𝓝[>] 0) atTop := by
    have hinv : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] 0) atTop := by
      first | exact tendsto_inv_nhdsGT_zero | exact tendsto_inv_zero_atTop
    exact (Real.tendsto_log_atTop.comp hinv).congr fun t => by simp [one_div]
  have hq : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have he : Tendsto (fun t => epsT C t) (𝓝[>] 0) (𝓝 0) := by
    have h := (hq.comp hL).const_mul C
    rw [mul_zero] at h
    refine h.congr fun t => ?_
    simp only [Function.comp, epsT]
    ring
  have ha : ∀ᶠ t in 𝓝[>] (0:ℝ), |epsT C t| < 1 / 2 := by
    have h := he.abs
    rw [abs_zero] at h
    exact h.eventually (gt_mem_nhds (by norm_num))
  have hb : ∀ᶠ t in 𝓝[>] (0:ℝ), C * epsT C t < 1 := by
    have h := he.const_mul C
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨u, hu, hsub⟩ : ∃ u ∈ Set.Ioi (0:ℝ), Set.Ioc 0 u ⊆ {t | |epsT C t| < 1 / 2 ∧ C * epsT C t < 1} := by
    first | exact mem_nhdsGT_iff_exists_Ioc_subset.mp (ha.and hb) | exact mem_nhdsWithin_Ioi_iff_exists_Ioc_subset.mp (ha.and hb)
  refine ⟨u, hu, fun t ht htu => ?_⟩
  obtain ⟨h1, h2⟩ := hsub ⟨ht, htu⟩
  exact ⟨h1.le, h2.le⟩

private theorem contDiffAt_comp_chart_symm_of_smoothOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (U : Set X) (f : X → ℝ) (hU : IsOpen U) (hf : A.SmoothOn U f) (j : Fin A.n) (y : Fin e → ℂ)
    (hy : y ∈ (A.chart j).target) (hyU : (A.chart j).symm y ∈ U) :
    ContDiffAt ℝ 2 (f ∘ (A.chart j).symm) y := by
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target hU
  refine ((hf j).contDiffAt (hopen.mem_nhds ⟨hy, hyU⟩)).of_le ?_
  first | exact_mod_cast (le_top : ((2 : ℕ∞)) ≤ ⊤) | simp | decide

private theorem levi_add_mul {ι : Type} [Fintype ι] (F G : (ι → ℂ) → ℝ) (y w : ι → ℂ) (k : ℝ)
    (hF : ContDiffAt ℝ 2 F y) (hG : ContDiffAt ℝ 2 G y) :
    levi (fun z => F z + k * G z) y w = levi F y w + k * levi G y w := by
  have hF1 : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ F z :=
    (hF.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
  have hG1 : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ G z :=
    (hG.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
  have hD : (fderiv ℝ fun z => F z + k * G z) =ᶠ[𝓝 y] fun z => fderiv ℝ F z + k • fderiv ℝ G z := by
    filter_upwards [hF1, hG1] with z hz1 hz2
    exact (hz1.hasFDerivAt.add (hz2.hasFDerivAt.const_mul k)).fderiv
  have hF2 : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG2 : DifferentiableAt ℝ (fderiv ℝ G) y :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ fun z => F z + k * G z) y =
      fderiv ℝ (fderiv ℝ F) y + k • fderiv ℝ (fderiv ℝ G) y := by
    rw [hD.fderiv_eq]
    exact (hF2.hasFDerivAt.add (hG2.hasFDerivAt.const_smul k)).fderiv
  unfold levi
  rw [h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem levi_split {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ th : LocPot X)
    (u : X → ℝ) (hΘ : IsPotential A Θ) (hth : IsPotential A th) (hu : A.Smooth u) (ε c : ℝ) (x : X)
    (j : Fin A.n) (y : Fin e → ℂ) (hy : y ∈ (A.chart j).target)
    (h1 : (A.chart j).symm y ∈ th.U x) (h2 : (A.chart j).symm y ∈ Θ.U x) (w : Fin e → ℂ) :
    levi (fun z => th.φ x ((A.chart j).symm z) + u ((A.chart j).symm z) +
        c * Θ.φ x ((A.chart j).symm z)) y w =
      levi ((th + LocPot.ofFun u + Θ.rsmul ε).φ x ∘ (A.chart j).symm) y w +
        (c - ε) * levi (Θ.φ x ∘ (A.chart j).symm) y w := by
  have hthC := contDiffAt_comp_chart_symm_of_smoothOn A (th.U x) (th.φ x) (th.isOpen_U x) (hth.1 x) j y hy h1
  have hΘC := contDiffAt_comp_chart_symm_of_smoothOn A (Θ.U x) (Θ.φ x) (Θ.isOpen_U x) (hΘ.1 x) j y hy h2
  have huC := contDiffAt_comp_chart_symm_of_smoothOn A Set.univ u isOpen_univ hu j y hy trivial
  have hPC : ContDiffAt ℝ 2 ((th + LocPot.ofFun u + Θ.rsmul ε).φ x ∘ (A.chart j).symm) y :=
    (hthC.add huC).add (contDiffAt_const.mul hΘC)
  rw [← levi_add_mul _ _ y w (c - ε) hPC hΘC]
  congr 1
  funext z
  show _ = th.φ x ((A.chart j).symm z) + u ((A.chart j).symm z) + ε * Θ.φ x ((A.chart j).symm z) +
    (c - ε) * Θ.φ x ((A.chart j).symm z)
  ring

private theorem levi_sub_const' {ι : Type} [Fintype ι] (g : (ι → ℂ) → ℝ) (a : ℝ) (y w : ι → ℂ) :
    levi (fun z => g z - a) y w = levi g y w := by
  have h : fderiv ℝ (fun z => g z - a) = fderiv ℝ g := by
    funext z
    by_cases hg : DifferentiableAt ℝ g z
    · exact (hg.hasFDerivAt.sub_const a).fderiv
    · have hg' : ¬ DifferentiableAt ℝ (fun z => g z - a) z := fun h => hg (by simpa using h.add_const a)
      rw [fderiv_zero_of_not_differentiableAt hg, fderiv_zero_of_not_differentiableAt hg']
  unfold levi
  rw [h]

private theorem levi_zero' {ι : Type} [Fintype ι] (g : (ι → ℂ) → ℝ) (y : ι → ℂ) : levi g y 0 = 0 := by
  unfold levi
  simp

theorem isPsh_of_le {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ th : LocPot X) (u : X → ℝ) (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ)
    (hth : IsPotential A th) (hu : A.Smooth u) (ε c a : ℝ) (hεc : ε ≤ c)
    (hP : IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε)) (Q : LocPot X)
    (hU : ∀ x, Q.U x ⊆ th.U x ∩ Θ.U x)
    (hφ : ∀ x z, Q.φ x z = th.φ x z + u z + c * Θ.φ x z - a) : IsPsh A Q := by
  intro x j y hy w
  obtain ⟨hyt, hyQ⟩ := hy
  have hsub := hU x hyQ
  have hfun : Q.φ x ∘ (A.chart j).symm = fun z => (th.φ x ((A.chart j).symm z) + u ((A.chart j).symm z) +
      c * Θ.φ x ((A.chart j).symm z)) - a := by
    funext z
    simp only [Function.comp_apply, hφ]
  rw [hfun, levi_sub_const' (fun z => th.φ x ((A.chart j).symm z) + u ((A.chart j).symm z) +
      c * Θ.φ x ((A.chart j).symm z)) a y w,
    levi_split A Θ th u hΘ hth hu ε c x j y hyt hsub.1 hsub.2 w]
  have hmem : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (th + LocPot.ofFun u + Θ.rsmul ε).U x := by
    refine ⟨hyt, ?_⟩
    show (A.chart j).symm y ∈ th.U x ∩ Set.univ ∩ Θ.U x
    exact ⟨⟨hsub.1, trivial⟩, hsub.2⟩
  have hPs := hP x j y hmem w
  rcases eq_or_ne w 0 with rfl | hw
  · simp [levi_zero']
  · have hΘp := hpos x j y ⟨hyt, hsub.2⟩ w hw
    have hce : 0 ≤ c - ε := sub_nonneg.mpr hεc
    nlinarith

theorem isPosPot_of_lt {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ th : LocPot X) (u : X → ℝ) (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ)
    (hth : IsPotential A th) (hu : A.Smooth u) (ε c : ℝ) (hεc : ε < c)
    (hP : IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε)) (Q : LocPot X)
    (hU : ∀ x, Q.U x ⊆ th.U x ∩ Θ.U x)
    (hφ : ∀ x z, Q.φ x z = th.φ x z + u z + c * Θ.φ x z) : IsPosPot A Q := by
  intro x j y hy w hw
  obtain ⟨hyt, hyQ⟩ := hy
  have hsub := hU x hyQ
  have hfun : Q.φ x ∘ (A.chart j).symm = fun z => th.φ x ((A.chart j).symm z) + u ((A.chart j).symm z) +
      c * Θ.φ x ((A.chart j).symm z) := by
    funext z
    simp only [Function.comp_apply, hφ]
  rw [hfun, levi_split A Θ th u hΘ hth hu ε c x j y hyt hsub.1 hsub.2 w]
  have hmem : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (th + LocPot.ofFun u + Θ.rsmul ε).U x := by
    refine ⟨hyt, ?_⟩
    show (A.chart j).symm y ∈ th.U x ∩ Set.univ ∩ Θ.U x
    exact ⟨⟨hsub.1, trivial⟩, hsub.2⟩
  have hPs := hP x j y hmem w
  have hΘp := hpos x j y ⟨hyt, hsub.2⟩ w hw
  have hce : 0 < c - ε := sub_pos.mpr hεc
  nlinarith

private theorem isPotential_add' {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P Q : LocPot X) (hP : IsPotential A P) (hQ : IsPotential A Q) : IsPotential A (P + Q) := by
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · show ContDiffOn ℝ _ (fun z => P.φ x ((A.chart j).symm z) + Q.φ x ((A.chart j).symm z))
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U x ∩ Q.U x))
    exact ((hP.1 x j).mono fun z (hz : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U x ∩ Q.U x)) =>
      ⟨hz.1, hz.2.1⟩).add ((hQ.1 x j).mono fun z
        (hz : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U x ∩ Q.U x)) => ⟨hz.1, hz.2.2⟩)
  · obtain ⟨⟨hPx, hQx⟩, hPx', hQx'⟩ := hy
    obtain ⟨W1, hW1o, hyW1, G1, hG1, hd1⟩ := hP.2 x x' y ⟨hPx, hPx'⟩
    obtain ⟨W2, hW2o, hyW2, G2, hG2, hd2⟩ := hQ.2 x x' y ⟨hQx, hQx'⟩
    refine ⟨W1 ∩ W2, hW1o.inter hW2o, ⟨hyW1, hyW2⟩, fun z => G1 z + G2 z, fun j => ?_, fun z hz => ?_⟩
    · exact ((hG1 j).mono fun z (hz : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (W1 ∩ W2)) =>
        ⟨hz.1, hz.2.1⟩).add ((hG2 j).mono fun z
          (hz : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (W1 ∩ W2)) => ⟨hz.1, hz.2.2⟩)
    · obtain ⟨⟨⟨hz1, hz2⟩, hzPx, hzQx⟩, hzPx', hzQx'⟩ := hz
      have e1 := hd1 z ⟨⟨hz1, hzPx⟩, hzPx'⟩
      have e2 := hd2 z ⟨⟨hz2, hzQx⟩, hzQx'⟩
      show P.φ x z + Q.φ x z - (P.φ x' z + Q.φ x' z) = (G1 z + G2 z).re
      rw [Complex.add_re, ← e1, ← e2]
      ring

theorem fixedMember_base : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C₅ C t₀ : ℝ), IsPotential A Θ → IsPosPot A Θ → (∀ y, logNormSec L s y ≤ 0) → IsSingWeight A L s th ph C₅ → IsRegFamily A Θ L s th ph phT C t₀ → ∃ t₂ : ℝ, 0 < t₂ ∧ t₂ ≤ t₀ ∧ ∀ t₁, 0 < t₁ → t₁ ≤ t₂ → IsPotential A (th + LocPot.ofFun (phT t₁) + Θ) ∧ IsPsh A (th + LocPot.ofFun (phT t₁) + Θ + Θ.rsmul (-(1 / 2))) ∧ IsPosPot A (th + LocPot.ofFun (phT t₁) + Θ) ∧ ∀ t, 0 < t → t ≤ t₁ → A.Smooth (fun y => phT t y - phT t₁ y - C * epsT C t₁) ∧ IsPsh A (th + LocPot.ofFun (phT t₁) + Θ + LocPot.ofFun (fun y => phT t y - phT t₁ y - C * epsT C t₁)) ∧ (∀ y, phT t y - phT t₁ y - C * epsT C t₁ ≤ 0) ∧ ∀ y ∉ bdry s, -(|C₅| + |C| + 1) * Real.log (rW L s y) ≤ phT t y - phT t₁ y - C * epsT C t₁ := by
  intro e X _ A Θ L s th ph phT C₅ C t₀ hΘ hpos hlog hSW hRF
  obtain ⟨a, ha, hab⟩ := epsT_small C
  obtain ⟨ht0, -, hR⟩ := hRF
  obtain ⟨hthP, -, -, hSW4⟩ := hSW
  refine ⟨min t₀ a, lt_min ht0 ha, min_le_left _ _, fun t₁ ht₁ ht₁2 => ?_⟩
  have ht₁0 : t₁ ≤ t₀ := ht₁2.trans (min_le_left _ _)
  have ht₁a : t₁ ≤ a := ht₁2.trans (min_le_right _ _)
  obtain ⟨hsm1, hC1, -, -, hpsh1, -, -, -⟩ := hR t₁ ht₁ ht₁0
  obtain ⟨he1, he1'⟩ := hab t₁ ht₁ ht₁a
  have hepsle : epsT C t₁ ≤ 1 / 2 := (le_abs_self _).trans he1
  refine ⟨isPotential_add' A _ _ (isPotential_add' A _ _ hthP (isPotential_ofFun A _ hsm1)) hΘ,
    ?_, ?_, fun t ht htt₁ => ?_⟩
  · exact isPsh_of_le A Θ th (phT t₁) hΘ hpos hthP hsm1 (epsT C t₁) (1 / 2) 0 hepsle hpsh1 _
      (fun x z (hz : z ∈ th.U x ∩ Set.univ ∩ Θ.U x ∩ Θ.U x) => ⟨hz.1.1.1, hz.1.2⟩)
      (fun x z => by
        show th.φ x z + phT t₁ z + Θ.φ x z + -(1 / 2) * Θ.φ x z = th.φ x z + phT t₁ z + 1 / 2 * Θ.φ x z - 0
        ring)
  · exact isPosPot_of_lt A Θ th (phT t₁) hΘ hpos hthP hsm1 (epsT C t₁) 1 (by linarith) hpsh1 _
      (fun x z (hz : z ∈ th.U x ∩ Set.univ ∩ Θ.U x) => ⟨hz.1.1, hz.2⟩)
      (fun x z => by
        show th.φ x z + phT t₁ z + Θ.φ x z = th.φ x z + phT t₁ z + 1 * Θ.φ x z
        ring)
  have htt0 : t ≤ t₀ := htt₁.trans ht₁0
  obtain ⟨hsm, -, hph, -, hpsh, -, -, hmono⟩ := hR t ht htt0
  obtain ⟨he, -⟩ := hab t ht (htt₁.trans ht₁a)
  have hepsle' : epsT C t ≤ 1 := by linarith [le_abs_self (epsT C t)]
  refine ⟨fun j => ((hsm j).sub (hsm1 j)).sub contDiffOn_const, ?_, fun y => ?_, fun y hy => ?_⟩
  · exact isPsh_of_le A Θ th (phT t) hΘ hpos hthP hsm (epsT C t) 1 (C * epsT C t₁) hepsle' hpsh _
      (fun x z (hz : z ∈ th.U x ∩ Set.univ ∩ Θ.U x ∩ Set.univ) => ⟨hz.1.1.1, hz.1.2⟩)
      (fun x z => by
        show th.φ x z + phT t₁ z + Θ.φ x z + (phT t z - phT t₁ z - C * epsT C t₁) =
          th.φ x z + phT t z + 1 * Θ.φ x z - C * epsT C t₁
        ring)
  · have h := hmono t₁ htt₁ ht₁0 y
    linarith
  · have h1 := hph y hy
    have h2 := (hSW4 y hy).1
    have h3 := hC1 y
    have hr : Real.exp 1 ≤ rW L s y := by
      have := hlog y
      unfold rW
      linarith
    have hL : 1 ≤ Real.log (rW L s y) := by
      have h := Real.log_le_log (Real.exp_pos 1) hr
      rwa [Real.log_exp] at h
    have k1 : 0 ≤ (|C₅| - C₅) * Real.log (rW L s y) :=
      mul_nonneg (sub_nonneg.mpr (le_abs_self C₅)) (by linarith)
    have k2 : 0 ≤ (|C| + 1) * (Real.log (rW L s y) - 1) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hL)
    have k3 := le_abs_self C
    nlinarith

end GlobalTheory.CompanionTheory.Ar.Giv
