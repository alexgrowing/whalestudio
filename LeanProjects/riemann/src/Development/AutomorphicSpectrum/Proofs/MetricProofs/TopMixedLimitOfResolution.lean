import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTTop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuRegSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHoloInjDerivInj
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PProjSmoothAlong
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalSectionOfPotentialOnModelStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalOrbitChartStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicSectionOfPotentialStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightPshAndBoundsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightTendstoC2Statement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularChartDataPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionNumberTelescopingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightUniformOnCompactStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PshDoublePositivePotentialStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeMetricFormulaStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalSectionVerticalFactorStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralLimitOnModelStatement

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

namespace Mix

section
variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

def GoodAt (X : ComponentSetting D O Lt) (B : ℕ) (Θ : LocPot X.M.Xc) (C₁ t : ℝ) : Prop :=
  IsSmoothHerm (muReg X.H X.S B t) ∧ X.M.atlas.Smooth (X.S.regWeight t) ∧
    (∀ x ∈ X.S.R.Yo, X.S.R.ph x ≤ X.S.regWeight t x ∧ X.S.regWeight t x ≤ C₁) ∧
    IsPsh X.M.atlas (X.S.R.th + LocPot.ofFun (X.S.regWeight t) + Θ)

theorem tendstoUniformlyOn_const' {α β : Type*} [UniformSpace β] (F : α → β) (s : Set α) :
    TendstoUniformlyOn (fun _ : ℝ => F) F (𝓝[>] 0) s := fun _ hu =>
  Eventually.of_forall fun _ _ _ => mem_uniformity_of_eq hu rfl

theorem regWeight_bound (X : ComponentSetting D O Lt) {C₁ v : ℝ} {x : X.M.Xc} (hx : x ∈ X.S.R.Yo)
    (h1 : X.S.R.ph x ≤ v) (h2 : v ≤ C₁) :
    |v| ≤ (|C₁| + |X.S.R.Clog|) + (|C₁| + |X.S.R.Clog|) * Real.log (X.S.R.r x) := by
  have hr : 0 ≤ Real.log (X.S.R.r x) := Real.log_nonneg (X.S.R.one_le_r x hx)
  have h3 := X.S.R.ph_ge x hx
  have h4 : X.S.R.Clog * Real.log (X.S.R.r x) ≤ |X.S.R.Clog| * Real.log (X.S.R.r x) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hr
  have h5 : |C₁| * 0 ≤ |C₁| * Real.log (X.S.R.r x) := mul_le_mul_of_nonneg_left hr (abs_nonneg _)
  have h6 : 0 ≤ |X.S.R.Clog| * Real.log (X.S.R.r x) := mul_nonneg (abs_nonneg _) hr
  have h7 := le_abs_self C₁
  have h8 := abs_nonneg C₁
  have h9 := abs_nonneg X.S.R.Clog
  rw [abs_le]
  constructor <;> nlinarith

theorem log_vert_prod (M : XModel D) (U : Set M.Xc) (σ : M.Xc → (Σ k, ι k) → ℂ) (hU : IsOpen U)
    (hσ : ∀ y ∈ U, σ y ∈ mcPts (mCoordIdeal D.y)) (hh : ∀ q, M.atlas.HoloOn U fun y => σ y q) {y₀ : M.Xc}
    (hy₀ : y₀ ∈ U) (s : Finset ℕ) (hs : s ⊆ D.S) :
    ∃ V : Set M.Xc, IsOpen V ∧ y₀ ∈ V ∧ V ⊆ U ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn V G ∧
      ∀ y ∈ V, Real.log (∏ p ∈ s, D.vertFactor p (σ y)) = (G y).re := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨U, hU, hy₀, subset_rfl, fun _ => 0, fun _ => analyticOnNhd_const, fun y _ => by simp⟩
  | insert p s hp ih =>
    have hpS : p ∈ D.S := hs (Finset.mem_insert_self p s)
    obtain ⟨V₁, hV₁, hy₁, hVU₁, G₁, hG₁, hl₁⟩ :=
      GlobalTheory.T.local_section_vertical_factor II Ψ K ι Ω E D p M U σ hpS hU hσ hh y₀ hy₀
    obtain ⟨V₂, hV₂, hy₂, hVU₂, G₂, hG₂, hl₂⟩ := ih fun q hq => hs (Finset.mem_insert_of_mem hq)
    refine ⟨V₁ ∩ V₂, hV₁.inter hV₂, ⟨hy₁, hy₂⟩, fun y hy => hVU₁ hy.1, fun y => G₁ y + G₂ y, fun j => ?_,
      fun y hy => ?_⟩
    · exact ((hG₁ j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left))).add
        ((hG₂ j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_right)))
    · have hz := hσ y (hVU₁ hy.1)
      have hpos : ∀ q ∈ D.S, 0 < D.vertFactor q (σ y) := fun q hq =>
        VertFactorPos.proof II Ψ K ι Ω E D q hq _ hz
      rw [Finset.prod_insert hp, Real.log_mul (hpos p hpS).ne'
        (Finset.prod_pos fun q hq => hpos q (hs (Finset.mem_insert_of_mem hq))).ne', hl₁ y hy.1, hl₂ y hy.2,
        Complex.add_re]

theorem reg_rel (X : ComponentSetting D O Lt) (B : ℕ) (t : ℝ) (x : X.M.Xc) :
    ∀ y₀ ∈ (X.S.R.th + LocPot.ofFun (X.S.regWeight t)).U x ∩ Set.univ, ∃ U : Set X.M.Xc, IsOpen U ∧ y₀ ∈ U ∧
      U ⊆ (X.S.R.th + LocPot.ofFun (X.S.regWeight t)).U x ∩ Set.univ ∧ ∃ s : X.M.Xc → (Σ k, ι k) → ℂ,
        (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ X.M.proj (s y') = y') ∧
        (∀ p, X.M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : X.M.Xc → ℂ, X.M.atlas.HoloOn U G ∧
          ∀ y' ∈ U, (X.S.R.th + LocPot.ofFun (X.S.regWeight t)).φ x y' -
            Real.log ((muReg X.H X.S B t).h (s y')) = (G y').re := by
  intro y₀ hy
  obtain ⟨U₀, hU₀, hy₀, hsub, s, hs, hh, G₀, hG₀, hrel⟩ := X.S.th_ref x y₀ hy.1.1
  obtain ⟨V, hV, hyV, hVU, Gv, hGv, hlog⟩ := log_vert_prod X.M U₀ s hU₀ (fun y h => (hs y h).1) hh hy₀
    (D.SB B) (Finset.filter_subset _ _)
  refine ⟨V, hV, hyV, fun y h => ⟨⟨hsub (hVU h), trivial⟩, trivial⟩, s, fun y h => hs y (hVU h),
    fun p j => (hh p j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU)), fun y => G₀ y - Gv y,
    fun j => ((hG₀ j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))).sub (hGv j), fun y' hy' => ?_⟩
  have hz := (hs y' (hVU hy')).1
  have hvp : 0 < ∏ p ∈ D.SB B, D.vertFactor p (s y') :=
    Finset.prod_pos fun p hp => VertFactorPos.proof II Ψ K ι Ω E D p (Finset.mem_filter.1 hp).1 _ hz
  have h1 := hrel y' (hVU hy')
  have h2 := hlog y' hy'
  have hproj := (hs y' (hVU hy')).2
  show X.S.R.th.φ x y' + X.S.regWeight t y' - _ = _
  rw [GlobalTheory.T.regularized_hodge_metric_formula II Ψ K ι Ω E D O Lt X B t (s y') hz, Real.log_mul
    (mul_pos (X.S.ref.pos _ hz.1) (Real.exp_pos _)).ne' hvp.ne', Real.log_mul (X.S.ref.pos _ hz.1).ne'
    (Real.exp_pos _).ne', Real.log_exp, hproj, h2, Complex.sub_re]
  linarith

theorem term_tendsto (X : ComponentSetting D O Lt) (B : ℕ) (Θ : LocPot X.M.Xc) (C₁ t₀ : ℝ) (k i : ℕ)
    (hΘ : IsPotential X.M.atlas Θ) (hΘp : IsPosPot X.M.atlas Θ)
    (hrel : ∀ x, ∀ y₀ ∈ Θ.U x ∩ Set.univ, ∃ U : Set X.M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ Θ.U x ∩ Set.univ ∧
      ∃ s : X.M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ X.M.proj (s y') = y') ∧
        (∀ p, X.M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : X.M.Xc → ℂ, X.M.atlas.HoloOn U G ∧
          ∀ y' ∈ U, Θ.φ x y' - (fun z => Real.log (D.A'.h z)) (s y') = (G y').re)
    (hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), GoodAt X B Θ C₁ t) (h₀ : GoodAt X B Θ C₁ t₀) :
    ∃ l : ℝ, Tendsto (fun t => ptsIntegral (mCoordIdeal D.y)
      (pot (mixWord (n := D.n) (muReg X.H X.S B t) (muReg X.H X.S B t₀) D.A' k i))
      (logRatio (muReg X.H X.S B t) (muReg X.H X.S B t₀))) (𝓝[>] 0) (𝓝 l) := by
  classical
  set R := X.S.R with hR
  set φ := X.S.regWeight with hφ
  set b := |C₁| + |R.Clog| with hb
  have hb0 : 0 ≤ b := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hrpos : ∀ x ∈ R.Yo, 0 ≤ Real.log (R.r x) := fun x hx => Real.log_nonneg (R.one_le_r x hx)
  have hth : IsPotential X.M.atlas R.th := R.th_pot
  let Pp : Fin D.n → LocPot X.M.Xc := fun j => if (j : ℕ) < i ∨ (j : ℕ) + 1 < k then R.th else Θ
  let f : Fin D.n → X.M.Xc → ℝ := fun j =>
    if (j : ℕ) < i then R.ph else if (j : ℕ) + 1 < k then φ t₀ else fun _ => 0
  let fT : Fin D.n → ℝ → X.M.Xc → ℝ := fun j t =>
    if (j : ℕ) < i then φ t else if (j : ℕ) + 1 < k then φ t₀ else fun _ => 0
  have hcases : ∀ j : Fin D.n, ((j : ℕ) < i ∧ Pp j = R.th ∧ f j = R.ph ∧ ∀ t, fT j t = φ t) ∨
      (¬ (j : ℕ) < i ∧ (j : ℕ) + 1 < k ∧ Pp j = R.th ∧ f j = φ t₀ ∧ ∀ t, fT j t = φ t₀) ∨
      (¬ (j : ℕ) < i ∧ ¬ (j : ℕ) + 1 < k ∧ Pp j = Θ ∧ f j = (fun _ => 0) ∧ ∀ t, fT j t = fun _ => 0) := by
    intro j
    by_cases h1 : (j : ℕ) < i
    · exact Or.inl ⟨h1, by simp [Pp, h1], by simp [f, h1], fun t => by simp [fT, h1]⟩
    · by_cases h2 : (j : ℕ) + 1 < k
      · exact Or.inr (Or.inl ⟨h1, h2, by simp [Pp, h2], by simp [f, h1, h2], fun t => by simp [fT, h1, h2]⟩)
      · exact Or.inr (Or.inr ⟨h1, h2, by simp [Pp, h1, h2], by simp [f, h1, h2], fun t => by simp [fT, h1, h2]⟩)
  have hbd' : ∀ x ∈ R.Yo, ∀ v, R.ph x ≤ v → v ≤ C₁ → |v| ≤ b + b * Real.log (R.r x) :=
    fun x hx v h1 h2 => regWeight_bound X hx h1 h2
  have hbd : ∀ x ∈ R.Yo, ∀ v, R.ph x ≤ v → v ≤ C₁ → |v| ≤ 2 * b + 2 * b * Real.log (R.r x) ∧ v ≤ 2 * b := by
    intro x hx v h1 h2
    have h3 := hbd' x hx v h1 h2
    have h4 := mul_nonneg hb0 (hrpos x hx)
    have h5 : C₁ ≤ b := (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
    constructor <;> nlinarith
  have hsm0 : X.M.atlas.Smooth (fun _ : X.M.Xc => (0 : ℝ)) := fun _ => contDiffOn_const
  have hYo : IsOpen R.Yo := (GlobalTheory.T.regular_chart_data_properties D.n X.M.Xc X.M.atlas R).1
  refine GlobalTheory.T.mixed_integral_limit_on_model K ι (mCoordIdeal D.y) D.n X.M R Θ Pp f fT (fun x => φ t₀ x - R.ph x)
    (fun t x => φ t₀ x - φ t x) (2 * b)
    (fun t => mixWord (n := D.n) (muReg X.H X.S B t) (muReg X.H X.S B t₀) D.A' k i)
    (fun t => logRatio (muReg X.H X.S B t) (muReg X.H X.S B t₀)) D.arith hΘ hΘp ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    rcases hcases j with ⟨-, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> rw [h]
    · exact hth
    · exact hth
    · exact hΘ
  · intro j
    rcases hcases j with ⟨-, -, h, -⟩ | ⟨-, -, -, h, -⟩ | ⟨-, -, -, h, -⟩ <;> rw [h]
    · exact R.ph_smooth
    · exact fun c => (h₀.2.1 c).mono (fun y hy => ⟨hy.1, Set.mem_univ _⟩)
    · exact fun c => contDiffOn_const
  · filter_upwards [hev] with t ht j
    rcases hcases j with ⟨-, hP, -, hT⟩ | ⟨-, -, hP, -, hT⟩ | ⟨-, -, hP, -, hT⟩ <;> rw [hP, hT t]
    · exact ⟨ht.2.1, ht.2.2.2, fun x hx => hbd x hx _ (ht.2.2.1 x hx).1 (ht.2.2.1 x hx).2⟩
    · exact ⟨h₀.2.1, h₀.2.2.2, fun x hx => hbd x hx _ (h₀.2.2.1 x hx).1 (h₀.2.2.1 x hx).2⟩
    · refine ⟨hsm0, GlobalTheory.T.psh_double_positive_potential _ _ _ _ hΘ hΘp, fun x hx => ?_⟩
      have := hrpos x hx
      have h2 : 0 ≤ b * Real.log (R.r x) := mul_nonneg hb0 this
      simp only [abs_zero]
      constructor <;> nlinarith
  · intro j c K' hK' hc
    rcases hcases j with ⟨-, -, hf, hT⟩ | ⟨-, -, -, hf, hT⟩ | ⟨-, -, -, hf, hT⟩ <;> simp only [hT, hf]
    · exact GlobalTheory.T.regularized_weight_tendsto_C2 K ι (mCoordIdeal D.y) D.n X.M D.Xo (muLine X.H) X.S X.S_tied c K' hK' hc
    · exact ⟨tendstoUniformlyOn_const' _ _, tendstoUniformlyOn_const' _ _, tendstoUniformlyOn_const' _ _⟩
    · exact ⟨tendstoUniformlyOn_const' _ _, tendstoUniformlyOn_const' _ _, tendstoUniformlyOn_const' _ _⟩
  · filter_upwards [hev] with t ht
    refine ⟨fun c => (h₀.2.1 c).sub (ht.2.1 c), fun x hx => ?_⟩
    have h1 := hbd' x hx _ (h₀.2.2.1 x hx).1 (h₀.2.2.1 x hx).2
    have h2 := hbd' x hx _ (ht.2.2.1 x hx).1 (ht.2.2.1 x hx).2
    have h3 := abs_sub (φ t₀ x) (φ t x)
    nlinarith
  · intro K' hK' hc
    have hU := GlobalTheory.T.regularized_weight_uniform_on_compact K ι (mCoordIdeal D.y) D.n X.M D.Xo (muLine X.H) X.S X.S_tied K' hK' hc
    rw [Metric.tendstoUniformlyOn_iff] at hU ⊢
    intro ε hε
    filter_upwards [hU ε hε] with t ht x hx
    show dist (φ t₀ x - R.ph x) (φ t₀ x - φ t x) < ε
    rw [Real.dist_eq, sub_sub_sub_cancel_left, abs_sub_comm, ← Real.dist_eq]
    exact ht x hx
  · filter_upwards [hev] with t ht j x y₀ hy
    rcases hcases j with ⟨h1, hP, -, hT⟩ | ⟨h1, h2, hP, -, hT⟩ | ⟨h1, h2, hP, -, hT⟩
    · have hw : mixWord (n := D.n) (muReg X.H X.S B t) (muReg X.H X.S B t₀) D.A' k i j = muReg X.H X.S B t := by
        simp [mixWord, h1]
      simp only [hP, hT, hw] at hy ⊢
      exact reg_rel X B t x y₀ hy
    · have hw : mixWord (n := D.n) (muReg X.H X.S B t) (muReg X.H X.S B t₀) D.A' k i j = muReg X.H X.S B t₀ := by
        simp [mixWord, h1, h2]
      simp only [hP, hT, hw] at hy ⊢
      exact reg_rel X B t₀ x y₀ hy
    · have hw : mixWord (n := D.n) (muReg X.H X.S B t) (muReg X.H X.S B t₀) D.A' k i j = D.A' := by
        simp [mixWord, h1, h2]
      simp only [hP, hT, hw] at hy ⊢
      obtain ⟨U, hU, hyU, hsub, s, hs, hh, G, hG, hrelG⟩ := hrel x y₀ ⟨hy.1.1, trivial⟩
      refine ⟨U, hU, hyU, fun y hy' => ⟨⟨(hsub hy').1, trivial⟩, trivial⟩, s, hs, hh, G, hG, fun y' hy' => ?_⟩
      have := hrelG y' hy'
      show Θ.φ x y' + 0 - _ = _
      simpa using this
  · filter_upwards with t z hz
    have hvp : ∀ u : ℝ, 0 < ∏ p ∈ D.SB B, D.vertFactor p z := fun _ =>
      Finset.prod_pos fun p hp => VertFactorPos.proof II Ψ K ι Ω E D p (Finset.mem_filter.1 hp).1 z hz
    have hlog : ∀ u : ℝ, Real.log ((muReg X.H X.S B u).h z) = Real.log (X.S.ref.h z) + φ u (X.M.proj z) +
        Real.log (∏ p ∈ D.SB B, D.vertFactor p z) := by
      intro u
      rw [GlobalTheory.T.regularized_hodge_metric_formula II Ψ K ι Ω E D O Lt X B u z hz, Real.log_mul (mul_pos (X.S.ref.pos z hz.1) (Real.exp_pos _)).ne'
        (hvp 0).ne', Real.log_mul (X.S.ref.pos z hz.1).ne' (Real.exp_pos _).ne', Real.log_exp]
    unfold logRatio
    rw [if_pos hz.1, hlog, hlog]
    ring

end

end Mix

open Mix in

theorem mixed_limit : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → TopNMixedLimit.Statement := by
  intro _ II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B hII _ k hk
  obtain ⟨Θ, hΘ, hrel⟩ := GlobalTheory.T.local_holomorphic_section_of_potential K ι (mCoordIdeal D.y) D.n X.M D.A' D.A'_pos.1
  have hΘp := GlobalTheory.T.local_section_of_potential_on_model II Ψ K ι Ω E D X.M Θ hΘ hrel
  obtain ⟨-, ⟨C₁, hC₁⟩, hpsh⟩ := GlobalTheory.T.regularized_weight_psh_and_bounds K ι (mCoordIdeal D.y) D.n X.M D.Xo (muLine X.H) X.S Θ X.S_tied hΘ hΘp
  have hsm : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (muReg X.H X.S B t) :=
    MuRegSmooth.proof HermExtend.proof (ProjSmoothAlong.proof HoloInjDerivInj.proof GlobalTheory.T.local_orbit_chart_statement_holds)
      (VertFactorSmooth.proof VertFactorPos.proof) VertFactorPos.proof II Ψ K ι Ω E D O Lt X B
  have hone : Θ.rsmul 1 = Θ := by
    cases Θ
    simp [LocPot.rsmul]
  have hp1 := hpsh 1 one_pos
  rw [hone] at hp1
  have hgood : ∀ᶠ t in 𝓝[>] (0 : ℝ), GoodAt X B Θ C₁ t := by
    filter_upwards [hsm, hC₁, hp1] with t h1 h2 h3
    exact ⟨h1, h2.1, h2.2, h3⟩
  obtain ⟨t₀, h₀⟩ := hgood.exists
  have hterm := fun i => term_tendsto X B Θ C₁ t₀ k i hΘ hΘp hrel hgood h₀
  choose l hl using hterm
  refine ⟨X.mixN B k t₀ - ∑ i ∈ Finset.range k, l i, ?_⟩
  have hlim := (tendsto_const_nhds (x := X.mixN B k t₀)).sub (tendsto_finsetSum (Finset.range k) fun i _ => hl i)
  refine hlim.congr' ?_
  filter_upwards [hgood] with t ht
  have ha : ∀ u, (muReg X.H X.S B u).a = muTwDeg X.H B := fun u => smoothRep_a _ _
  have hT := GlobalTheory.T.intersection_number_telescoping K ι (II K ι) (hII K ι) (mCoordIdeal D.y) D.n (muReg X.H X.S B t) (muReg X.H X.S B t₀) D.A' k
    D.arith ht.1 h₀.1 D.A'_pos.1 ((ha t).trans (ha t₀).symm) (by omega)
  have hm : ∀ u, X.mixN B k u = II K ι (mCoordIdeal D.y) (D.n + 1)
      (fun j => if (j : ℕ) < k then muReg X.H X.S B u else D.A') := fun _ => rfl
  rw [hm t, hm t₀]
  linarith

end GlobalTheory.CompanionTheory.Ar.Giv
