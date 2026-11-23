import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

namespace Compare

open ReciprocityTheory.AnForm.P.RegularChartScaling

lemma exists_lip_near {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {Ω Z : Set E} {F : E → G} (hΩ : IsOpen Ω)
    (hZ : IsCompact Z) (hZΩ : Z ⊆ Ω) (hF : ContDiffOn ℝ 1 F Ω) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ∀ z ∈ Z, ∀ w ∈ closedBall z r,
      w ∈ Ω ∧ ‖F w - F z‖ ≤ L * ‖w - z‖ := by
  obtain ⟨δ, hδ, hsub⟩ := hZ.exists_cthickening_subset_open hΩ hZΩ
  have hK : IsCompact (cthickening δ Z) := hZ.cthickening
  have hcont : ContinuousOn (fderiv ℝ F) (cthickening δ Z) :=
    (hF.continuousOn_fderiv_of_isOpen hΩ le_rfl).mono hsub
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨δ, max L 0, hδ, le_max_right _ _, fun z hz w hw => ?_⟩
  have hball : closedBall z δ ⊆ cthickening δ Z := closedBall_subset_cthickening hz δ
  refine ⟨hsub (hball hw), ?_⟩
  exact (convex_closedBall z δ).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := F)
    (fun x hx => (hF.contDiffAt (hΩ.mem_nhds (hsub (hball hx)))).differentiableAt (by norm_num))
    (fun x hx => (hL x (hball hx)).trans (le_max_left _ _)) (mem_closedBall_self hδ.le) hw

lemma isClosed_coordDiv {D : ℕ} (S : Finset (Fin D)) :
    IsClosed (ReciprocityTheory.AnForm.A.coordDiv S) := by
  have : ReciprocityTheory.AnForm.A.coordDiv S = ⋃ i ∈ S, {z : Fin D → ℂ | z i = 0} := by
    ext z; simp [ReciprocityTheory.AnForm.A.coordDiv]
  rw [this]
  exact S.finite_toSet.isClosed_biUnion fun i _ => isClosed_eq (continuous_apply i) continuous_const

lemma overlap_pair {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] (B : FinHolAtlas e X)
    (j k : Fin B.n) (h2 : ∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target) (g : X → ℝ)
    (hg : ContDiffOn ℝ 1 (g ∘ (B.chart j).symm)
      ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (B.chart k).source)) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4),
      ∀ w ∈ closedBall (B.chart j y) r, w ∈ (B.chart j).target ∧
        (B.chart j).symm w ∈ (B.chart k).source ∧
        ‖B.chart k ((B.chart j).symm w) - B.chart k y‖ ≤ L * ‖w - B.chart j y‖ ∧
        |g ((B.chart j).symm w) - g y| ≤ L * ‖w - B.chart j y‖ := by
  have hsubB : ∀ i, closedBall (0 : Fin e → ℂ) (5 / 4) ⊆ (B.chart i).target := fun i =>
    (closedBall_subset_closedBall (by norm_num)).trans (h2 i)
  have hKi : ∀ i, IsCompact ((B.chart i).symm '' closedBall (0 : Fin e → ℂ) (5 / 4)) := fun i =>
    (isCompact_closedBall _ _).image_of_continuousOn ((B.chart i).continuousOn_symm.mono (hsubB i))
  set K : Set X := (B.chart j).symm '' closedBall (0 : Fin e → ℂ) (5 / 4) ∩
    (B.chart k).symm '' closedBall (0 : Fin e → ℂ) (5 / 4) with hKdef
  have hKc : IsCompact K := (hKi j).inter (hKi k)
  have hKj : K ⊆ (B.chart j).source := by
    rintro _ ⟨⟨z, hz, rfl⟩, -⟩
    exact (B.chart j).map_target (hsubB j hz)
  have hKk : K ⊆ (B.chart k).source := by
    rintro p ⟨-, ⟨z, hz, rfl⟩⟩
    exact (B.chart k).map_target (hsubB k hz)
  set Ω := (B.chart j).target ∩ (B.chart j).symm ⁻¹' (B.chart k).source with hΩdef
  have hΩ : IsOpen Ω := (B.chart j).isOpen_inter_preimage_symm (B.chart k).open_source
  have hZc : IsCompact (B.chart j '' K) :=
    hKc.image_of_continuousOn ((B.chart j).continuousOn.mono hKj)
  have hZΩ : B.chart j '' K ⊆ Ω := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨(B.chart j).map_source (hKj hp), ?_⟩
    rw [Set.mem_preimage, (B.chart j).left_inv (hKj hp)]
    exact hKk hp
  have hT : ContDiffOn ℝ 1 (B.chart k ∘ (B.chart j).symm) Ω := fun z hz =>
    (((B.holo j k z hz).contDiffAt (n := 1)).restrict_scalars ℝ).contDiffWithinAt
  obtain ⟨r, L, hr, hL, h⟩ := exists_lip_near hΩ hZc hZΩ (hT.prodMk hg)
  refine ⟨r, L, hr, hL, fun y hy w hw => ?_⟩
  have hyj : y ∈ (B.chart j).source := hy.1.1
  have hyk : y ∈ (B.chart k).source := hy.2.1
  have hyK : y ∈ K := by
    refine ⟨⟨B.chart j y, ball_subset_closedBall hy.1.2, (B.chart j).left_inv hyj⟩,
      ⟨B.chart k y, ball_subset_closedBall hy.2.2, (B.chart k).left_inv hyk⟩⟩
  obtain ⟨hwΩ, hb⟩ := h (B.chart j y) ⟨y, hyK, rfl⟩ w hw
  simp only [Function.comp, (B.chart j).left_inv hyj] at hb
  refine ⟨hwΩ.1, hwΩ.2, (norm_fst_le _).trans hb, ?_⟩
  have := (norm_snd_le _).trans hb
  simpa [Real.norm_eq_abs] using this

lemma le_log_div {t : ℝ} (ht : 0 < t) (hℓ : Real.exp 1 ≤ Real.log (1 / t)) :
    t ≤ Real.log (Real.log (1 / t)) / Real.log (1 / t) := by
  set ℓ := Real.log (1 / t) with hdef
  have he : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hℓ1 : 1 ≤ ℓ := he.trans hℓ
  have hlog : 1 ≤ Real.log ℓ := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hℓ
  have hexp : Real.exp ℓ = 1 / t := Real.exp_log (by positivity)
  have h1 : ℓ + 1 ≤ 1 / t := by rw [← hexp]; exact Real.add_one_le_exp ℓ
  rw [le_div_iff₀ (by linarith)]
  have h2 : ℓ * t ≤ 1 := by
    have : (ℓ + 1) * t ≤ (1 / t) * t := mul_le_mul_of_nonneg_right h1 ht.le
    rw [one_div, inv_mul_cancel₀ ht.ne'] at this
    nlinarith
  linarith

lemma epsT_mono {C C' t : ℝ} (h : C ≤ C') (hℓ : Real.exp 1 ≤ Real.log (1 / t)) :
    epsT C t ≤ epsT C' t := by
  unfold epsT
  have he : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlog : 1 ≤ Real.log (Real.log (1 / t)) := by
    have := Real.log_le_log (Real.exp_pos 1) hℓ
    rwa [Real.log_exp] at this
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h (by linarith)) (by linarith)

lemma epsT_add (a b t : ℝ) : epsT (a + b) t = epsT a t + epsT b t := by
  unfold epsT; ring

lemma chart_data {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X)
    (L th : LocPot X) (s : X → X → ℂ) (ph : X → ℝ) (C₅ M : ℝ) (j : Fin B.n) (xj : X)
    (S : Finset (Fin e)) (m : Fin e → ℕ) (hAB : A.Compatible B)
    (h2 : closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target)
    (hU : (B.chart j).source ⊆ th.U xj) (hle : ∀ y, logNormSec L s y ≤ 0)
    (hcl : IsClosed (bdry s))
    (hS : ∀ y ∈ (B.chart j).target, ((B.chart j).symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0))
    (hM : ∀ y ∈ closedBall (0 : Fin e → ℂ) 2, (B.chart j).symm y ∉ bdry s →
      |rW L s ((B.chart j).symm y) - rLoc S m y| ≤ M)
    (hW : IsSingWeight A L s th ph C₅) :
    ContinuousOn (fun z => th.φ xj ((B.chart j).symm z) + ph ((B.chart j).symm z))
        (ball 0 2 \ ReciprocityTheory.AnForm.A.coordDiv S) ∧
      ReciprocityTheory.AnForm.A.IsPsh (ball 0 2 \ ReciprocityTheory.AnForm.A.coordDiv S)
        (fun z => th.φ xj ((B.chart j).symm z) + ph ((B.chart j).symm z)) ∧
      ∃ C : ℝ, ∀ z ∈ ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv S,
        -C * Real.log (rLoc S m z) ≤ th.φ xj ((B.chart j).symm z) + ph ((B.chart j).symm z) ∧
        th.φ xj ((B.chart j).symm z) + ph ((B.chart j).symm z) ≤ C := by
  set V := ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv S with hV
  have hVo : IsOpen V := isOpen_ball.sdiff (isClosed_coordDiv S)
  have hVt : ∀ z ∈ V, z ∈ (B.chart j).target := fun z hz => h2 (ball_subset_closedBall hz.1)
  have hVb : ∀ z ∈ V, (B.chart j).symm z ∉ bdry s := fun z hz hb =>
    hz.2 ((hS z (hVt z hz)).1 hb)
  have hVU : ∀ z ∈ (B.chart j).target, (B.chart j).symm z ∈ th.U xj := fun z hz =>
    hU ((B.chart j).map_target hz)
  have hBth : B.SmoothOn (th.U xj) (th.φ xj) :=
    smoothOn_of_compatible hAB (th.isOpen_U xj) (hW.1.1 xj)
  have hBph : B.SmoothOn (bdry s)ᶜ ph :=
    smoothOn_of_compatible hAB hcl.isOpen_compl hW.2.1
  have hq : ContDiffOn ℝ ∞ (fun z => th.φ xj ((B.chart j).symm z)) (B.chart j).target :=
    (hBth j).mono fun z hz => ⟨hz, hVU z hz⟩
  have hu : ContDiffOn ℝ ∞ (fun z => th.φ xj ((B.chart j).symm z) + ph ((B.chart j).symm z)) V :=
    (hq.mono hVt).add ((hBph j).mono fun z hz => ⟨hVt z hz, hVb z hz⟩)
  have hu2 : ContDiffOn ℝ 2 (fun z => th.φ xj ((B.chart j).symm z) + ph ((B.chart j).symm z)) V :=
    hu.of_le (by norm_cast)
  refine ⟨hu.continuousOn, ?_, ?_⟩
  · refine (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm e V _ hVo hu2).2 ⟨hu2, fun z hz w => ?_⟩
    obtain ⟨k, ha, ht, hl, hf⟩ := compat_local hAB j (hVt z hz)
    set f : X → ℝ := (th + LocPot.ofFun ph).φ xj with hfdef
    set τ := A.chart k ∘ (B.chart j).symm with hτ
    have hO : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (th.U xj ∩ (bdry s)ᶜ)) :=
      (A.chart k).isOpen_inter_preimage_symm ((th.isOpen_U xj).inter hcl.isOpen_compl)
    have hmem : τ z ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (th.U xj ∩ (bdry s)ᶜ) := by
      refine ⟨ht, ?_⟩
      show (A.chart k).symm (A.chart k ((B.chart j).symm z)) ∈ th.U xj ∩ (bdry s)ᶜ
      rw [hl]
      exact ⟨hVU z (hVt z hz), hVb z hz⟩
    have hsm : ContDiffOn ℝ ∞ (f ∘ (A.chart k).symm)
        ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (th.U xj ∩ (bdry s)ᶜ)) :=
      ((hW.1.1 xj k).mono fun y hy => ⟨hy.1, hy.2.1⟩).add
        ((hW.2.1 k).mono fun y hy => ⟨hy.1, hy.2.2⟩)
    have hφ : ContDiffAt ℝ 2 (f ∘ (A.chart k).symm) (τ z) :=
      (hsm.contDiffAt (hO.mem_nhds hmem)).of_le (by norm_cast)
    have e1 : levi (fun z => th.φ xj ((B.chart j).symm z) + ph ((B.chart j).symm z)) z w =
        levi (f ∘ (A.chart k).symm) (τ z) (fderiv ℂ τ z w) := by
      rw [← levi_comp w ha hφ]
      exact levi_congr (hf f) w
    rw [e1]
    exact hW.2.2.1 xj k (τ z) ⟨hmem.1, ⟨hmem.2.1, trivial⟩, hmem.2.2⟩ _
  · obtain ⟨Q, hQ⟩ := (isCompact_closedBall (0 : Fin e → ℂ) 2).exists_bound_of_continuousOn
      (hq.continuousOn.mono h2)
    set Λ := Real.log (1 + |M|) with hΛ
    have hΛ0 : 0 ≤ Λ := Real.log_nonneg (by linarith [abs_nonneg M])
    refine ⟨|Q| + |C₅| * (1 + Λ) + |C₅|, fun z hz => ?_⟩
    set p := (B.chart j).symm z with hp
    have hzc : z ∈ closedBall (0 : Fin e → ℂ) 2 := ball_subset_closedBall hz.1
    have hq1 : |th.φ xj p| ≤ Q := by simpa [Real.norm_eq_abs] using hQ z hzc
    have hb := hM z hzc (hVb z hz)
    obtain ⟨hlo, hup⟩ := hW.2.2.2 p (hVb z hz)
    have hr1 : Real.exp 1 ≤ rLoc S m z := rLoc_ge S m (norm_coord_le_of_ball le_rfl hz.1)
    have hr2 : Real.exp 1 ≤ rW L s p := rW_ge L s hle p
    have hr0 : 0 < rLoc S m z := (Real.exp_pos 1).trans_le hr1
    have hw0 : 0 < rW L s p := (Real.exp_pos 1).trans_le hr2
    have hone : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hlr : 1 ≤ Real.log (rLoc S m z) := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hr1
    have hlw : 1 ≤ Real.log (rW L s p) := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hr2
    have hle1 : rW L s p ≤ rLoc S m z * (1 + |M|) := by
      have h1 := (abs_le.1 hb).2
      have h2' := le_abs_self M
      have : |M| ≤ rLoc S m z * |M| :=
        le_mul_of_one_le_left (abs_nonneg M) (hone.trans hr1)
      nlinarith
    have hlog : Real.log (rW L s p) ≤ (1 + Λ) * Real.log (rLoc S m z) := by
      have h1 : Real.log (rW L s p) ≤ Real.log (rLoc S m z) + Λ := by
        rw [hΛ, ← Real.log_mul hr0.ne' (by positivity)]
        exact Real.log_le_log hw0 hle1
      nlinarith
    have hC5l : -C₅ * Real.log (rW L s p) ≥ -(|C₅| * ((1 + Λ) * Real.log (rLoc S m z))) := by
      have h1 : C₅ * Real.log (rW L s p) ≤ |C₅| * Real.log (rW L s p) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      have h2' : |C₅| * Real.log (rW L s p) ≤ |C₅| * ((1 + Λ) * Real.log (rLoc S m z)) :=
        mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
      linarith
    have hq2 := abs_le.1 hq1
    have hQa := le_abs_self Q
    have hC5a := le_abs_self C₅
    have hm0 : 0 ≤ |C₅| * (1 + Λ) := mul_nonneg (abs_nonneg _) (by linarith)
    constructor
    · have e1 : |Q| ≤ |Q| * Real.log (rLoc S m z) :=
        le_mul_of_one_le_right (abs_nonneg _) hlr
      have e2 : 0 ≤ |C₅| * Real.log (rLoc S m z) :=
        mul_nonneg (abs_nonneg _) (by linarith)
      nlinarith
    · linarith

end Compare

open ReciprocityTheory.AnForm.P.RegularChartScaling in

theorem polyMaxOff_charts_compare {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas e X) (L th : LocPot X) (s : X → X → ℂ) (ph : X → ℝ) (C₅ M : ℝ) (x : Fin B.n → X) (S : Fin B.n → Finset (Fin e)) (m : Fin B.n → Fin e → ℕ) (hAB : A.Compatible B) (h2 : ∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target) (hU : ∀ j, (B.chart j).source ⊆ th.U (x j)) (hle : ∀ y, logNormSec L s y ≤ 0) (hcl : IsClosed (bdry s)) (hS : ∀ j, ∀ y ∈ (B.chart j).target, ((B.chart j).symm y ∈ bdry s ↔ ∃ i ∈ S j, y i = 0)) (hM : ∀ j, ∀ y ∈ closedBall (0 : Fin e → ℂ) 2, (B.chart j).symm y ∉ bdry s → |rW L s ((B.chart j).symm y) - rLoc (S j) (m j) y| ≤ M) (hW : IsSingWeight A L s th ph C₅) : ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t, 0 < t → t ≤ t₀ → ∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |(polyMaxOff (S j) (fun z => th.φ (x j) ((B.chart j).symm z) + ph ((B.chart j).symm z)) (B.chart j y) t - th.φ (x j) y) - (polyMaxOff (S k) (fun z => th.φ (x k) ((B.chart k).symm z) + ph ((B.chart k).symm z)) (B.chart k y) t - th.φ (x k) y)| ≤ epsT C t := by
  classical

  have hBth : ∀ i, B.SmoothOn (th.U (x i)) (th.φ (x i)) := fun i =>
    smoothOn_of_compatible hAB (th.isOpen_U (x i)) (hW.1.1 (x i))
  have hg : ∀ p : Fin B.n × Fin B.n,
      ContDiffOn ℝ 1 ((fun y => th.φ (x p.1) y - th.φ (x p.2) y) ∘ (B.chart p.1).symm)
        ((B.chart p.1).target ∩ (B.chart p.1).symm ⁻¹' (B.chart p.2).source) := by
    intro p
    have h1 : ContDiffOn ℝ ∞ (fun z => th.φ (x p.1) ((B.chart p.1).symm z) -
        th.φ (x p.2) ((B.chart p.1).symm z))
        ((B.chart p.1).target ∩ (B.chart p.1).symm ⁻¹' (B.chart p.2).source) := by
      refine ContDiffOn.sub ((hBth p.1 p.1).mono fun z hz => ⟨hz.1, hU p.1 ((B.chart p.1).map_target hz.1)⟩) ?_
      intro z hz

      exact ((smoothOn_of_compatible hAB (th.isOpen_U (x p.2)) (hW.1.1 (x p.2)) p.1).mono
        fun z hz => ⟨hz.1, hU p.2 hz.2⟩) z hz
    exact h1.of_le (by norm_cast)
  have hpair := fun p : Fin B.n × Fin B.n =>
    Compare.overlap_pair B p.1 p.2 h2 _ (hg p)
  choose r Lc hr hLc hov using hpair
  obtain ⟨Rinv, hRinv⟩ := Finite.exists_le (fun p => (r p)⁻¹)
  obtain ⟨L₀, hL₀⟩ := Finite.exists_le Lc
  set r₀ : ℝ := (max Rinv 1)⁻¹ with hr₀
  have hr₀0 : 0 < r₀ := inv_pos.2 (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hr₀le : ∀ p, r₀ ≤ r p := fun p => by
    rw [hr₀]
    exact inv_le_of_inv_le₀ (hr p) ((hRinv p).trans (le_max_left _ _))
  set C₁ : ℝ := max L₀ 1 with hC₁def
  have hC₁ : 1 ≤ C₁ := le_max_right _ _
  have hLC : ∀ p, Lc p ≤ C₁ := fun p => (hL₀ p).trans (le_max_left _ _)

  have hdata := fun i => Compare.chart_data A B L th s ph C₅ M i (x i) (S i) (m i) hAB (h2 i)
    (hU i) hle hcl (hS i) (hM i) hW
  choose hcont hpsh Cb hCb using hdata
  have hosc := fun i => oscGen (m i) (R := 2) (C₅ := Cb i) le_rfl (by norm_num) (hcont i) (hpsh i)
    (hCb i) hC₁
  choose Co ℓo hCo hosc using hosc
  obtain ⟨Cm, hCm⟩ := Finite.exists_le Co
  obtain ⟨ℓm, hℓm⟩ := Finite.exists_le ℓo
  refine ⟨C₁ + Cm, min (Real.exp (-ℓm)) r₀, lt_min (Real.exp_pos _) hr₀0, fun t ht htle => ?_⟩
  have hℓ : ℓm ≤ Real.log (1 / t) := by
    have h1 : Real.log t ≤ -ℓm := by
      have := Real.log_le_log ht (htle.trans (min_le_left _ _))
      rwa [Real.log_exp] at this
    rw [one_div, Real.log_inv]; linarith
  have hone : ∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4),
      polyMaxOff (S j) (fun z => th.φ (x j) ((B.chart j).symm z) + ph ((B.chart j).symm z))
          (B.chart j y) t - th.φ (x j) y -
        (polyMaxOff (S k) (fun z => th.φ (x k) ((B.chart k).symm z) + ph ((B.chart k).symm z))
          (B.chart k y) t - th.φ (x k) y) ≤ epsT (C₁ + Cm) t := by
    intro j k y hy
    obtain ⟨he, hCt, hz⟩ := hosc k t ht ((hℓm k).trans hℓ)
    obtain ⟨-, hoscz⟩ := hz (B.chart k y) hy.2.2
    set uk : (Fin e → ℂ) → ℝ := fun z => th.φ (x k) ((B.chart k).symm z) + ph ((B.chart k).symm z)
      with huk
    set uj : (Fin e → ℂ) → ℝ := fun z => th.φ (x j) ((B.chart j).symm z) + ph ((B.chart j).symm z)
      with huj
    set z' := B.chart k y with hz'
    set z := B.chart j y with hzdef
    have hub : ∀ w ∈ ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S k), uk w ≤ Cb k :=
      fun w hw => (hCb k w hw).2
    have hz'b : z' ∈ ball (0 : Fin e → ℂ) (5 / 4) := hy.2.2
    have hsub : ∀ σ, σ ≤ (2 - 5 / 4 : ℝ) → closedBall z' σ ⊆ ball 0 2 := fun σ hσ =>
      closedBall_sub_of hz'b (by linarith)
    have ht1 : t ≤ C₁ * t := le_mul_of_one_le_left ht.le hC₁
    have hCt' : C₁ * t ≤ (2 - 5 / 4 : ℝ) := by linarith [mul_pos (lt_of_lt_of_le one_pos hC₁) ht]
    have hC₁0 : 0 < C₁ := lt_of_lt_of_le one_pos hC₁
    have hsmall : t / (4 * C₁) ≤ t := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hmono : pmoff (S k) uk z' (t / (4 * C₁)) ≤ pmoff (S k) uk z' t :=
      pmo_mono hub (by positivity) hsmall (hsub t (by linarith))

    have hkey : pmoff (S j) uj z t ≤
        pmoff (S k) uk z' (C₁ * t) + (th.φ (x j) y - th.φ (x k) y) + C₁ * t := by
      refine pmo_le z ht fun w hw => ?_
      have hwr : w ∈ closedBall z (r (j, k)) :=
        closedBall_subset_closedBall ((htle.trans (min_le_right _ _)).trans (hr₀le _)) hw.1
      obtain ⟨hwt, hws, hw1, hw2⟩ := hov (j, k) y hy w hwr
      have hnorm : ‖w - z‖ ≤ t := by simpa [dist_eq_norm] using hw.1
      have hLc0 := hLc (j, k)
      have hbound : Lc (j, k) * ‖w - z‖ ≤ C₁ * t :=
        mul_le_mul (hLC _) hnorm (norm_nonneg _) hC₁0.le
      set p := (B.chart j).symm w with hp
      have hpb : p ∉ bdry s := fun hb => hw.2 ((hS j w hwt).1 hb)
      set w' := B.chart k p with hw'
      have hw't : w' ∈ (B.chart k).target := (B.chart k).map_source hws
      have hpw' : (B.chart k).symm w' = p := (B.chart k).left_inv hws
      have hw'off : w' ∉ ReciprocityTheory.AnForm.A.coordDiv (S k) := fun hc =>
        hpb (hpw' ▸ (hS k w' hw't).2 hc)
      have hw'ball : w' ∈ closedBall z' (C₁ * t) := by
        rw [mem_closedBall, dist_eq_norm]
        exact hw1.trans hbound
      have hle1 : uk w' ≤ pmoff (S k) uk z' (C₁ * t) :=
        le_pmo hub (hsub _ hCt') ⟨hw'ball, hw'off⟩
      have huk' : uk w' = th.φ (x k) p + ph p := by simp only [huk, hpw']
      have hg1 := (abs_le.1 (hw2.trans hbound)).2
      show th.φ (x j) p + ph p ≤ _
      simp only at hg1
      linarith
    have hL : C₁ * t ≤ epsT C₁ t := by
      have := Compare.le_log_div ht he
      have h3 := mul_le_mul_of_nonneg_left this hC₁0.le
      unfold epsT
      rwa [mul_div_assoc]
    have hCk : epsT (Co k) t ≤ epsT Cm t := Compare.epsT_mono (hCm k) he
    have hsum := Compare.epsT_add C₁ Cm t
    show pmoff (S j) uj z t - _ - (pmoff (S k) uk z' t - _) ≤ _
    linarith
  intro j k y hy
  rw [abs_le]
  constructor
  · have := hone k j y ⟨hy.2, hy.1⟩
    linarith
  · exact hone j k y hy

end GlobalTheory.CompanionTheory.Ar.Giv
