import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PositionPot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralModelFormulaStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularChartDataPropertiesStatement
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNbarLeviChartReg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

section Local

variable {e : ℕ} {X : Type} [TopologicalSpace X] {I : Type} [Fintype I]

theorem holoOn_mono (A : FinHolAtlas e X) {U V : Set X} {g : X → ℂ} (h : A.HoloOn U g) (hs : V ⊆ U) :
    A.HoloOn V g :=
  fun j w hw => h j w ⟨hw.1, hs hw.2⟩

theorem continuousOn_of_holoOn (A : FinHolAtlas e X) {U : Set X} {s : X → I → ℂ}
    (hU : IsOpen U) (hs : ∀ p, A.HoloOn U fun y => s y p) : ContinuousOn s U := by
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  refine ContinuousAt.continuousWithinAt (continuousAt_pi.2 fun p => ?_)
  have hw : A.chart j y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hj, by
      show (A.chart j).symm (A.chart j y) ∈ U
      rw [(A.chart j).left_inv hj]; exact hy⟩
  have h1 : ContinuousAt ((fun y => s y p) ∘ (A.chart j).symm) (A.chart j y) :=
    (hs p j _ hw).continuousAt
  have h2 : ContinuousAt (A.chart j) y := (A.chart j).continuousAt hj
  have h3 : ContinuousAt (((fun y => s y p) ∘ (A.chart j).symm) ∘ A.chart j) y :=
    ContinuousAt.comp h1 h2
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y' hy'
  simp [(A.chart j).left_inv hy']

theorem log_norm_section_local (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U) {s : X → I → ℂ}
    (hs : ∀ p, A.HoloOn U fun y => s y p) {y₀ : X} (hy₀ : y₀ ∈ U) {T : (I → ℂ) → ℂ}
    (hT : AnalyticAt ℂ T (s y₀)) (hT0 : T (s y₀) ≠ 0) {Q : (I → ℂ) → Prop}
    (hQ : ∀ᶠ z in 𝓝 (s y₀), Q z) :
    ∃ U' : Set X, IsOpen U' ∧ y₀ ∈ U' ∧ U' ⊆ U ∧ (∀ y ∈ U', Q (s y)) ∧ ∃ G : X → ℂ, A.HoloOn U' G ∧
      ∀ y ∈ U', Real.log ‖T (s y)‖ = (G y).re := by
  set L : (I → ℂ) → ℂ := fun z => Complex.log (T z / T (s y₀)) with hL
  have hLa : AnalyticAt ℂ L (s y₀) := by
    refine (hT.div analyticAt_const hT0).clog ?_
    simp [hT0]
  have hev : ∀ᶠ z in 𝓝 (s y₀), AnalyticAt ℂ L z ∧ T z ≠ 0 ∧ Q z :=
    hLa.eventually_analyticAt.and ((hT.continuousAt.eventually_ne hT0).and hQ)
  obtain ⟨N, hNsub, hNo, hzN⟩ := mem_nhds_iff.1 hev
  have hc := continuousOn_of_holoOn A hU hs
  refine ⟨U ∩ s ⁻¹' N, hc.isOpen_inter_preimage hU hNo, ⟨hy₀, hzN⟩, Set.inter_subset_left,
    fun y hy => (hNsub hy.2).2.2, fun y => L (s y) + (Real.log ‖T (s y₀)‖ : ℂ), ?_, ?_⟩
  · intro j w hw
    have hsw : AnalyticAt ℂ (fun w => s ((A.chart j).symm w)) w :=
      analyticAt_pi_iff.2 fun p => hs p j w ⟨hw.1, hw.2.1⟩
    have hcomp : AnalyticAt ℂ (fun w => L (s ((A.chart j).symm w))) w :=
      AnalyticAt.comp' (hNsub hw.2.2).1 hsw
    exact hcomp.add analyticAt_const
  · intro y hy
    have hTy := (hNsub hy.2).2.1
    simp only [hL, Complex.add_re, Complex.ofReal_re, Complex.log_re, norm_div]
    rw [Real.log_div (norm_ne_zero_iff.2 hTy) (norm_ne_zero_iff.2 hT0)]
    ring

end Local

section Slots

variable {X : Type} [TopologicalSpace X] {e : ℕ}

theorem positionPot_lt (th Pn : LocPot X) (f : X → ℝ) {i : ℕ} {j : Fin e} (hj : (j : ℕ) < i) :
    positionPot th Pn f i j = th + LocPot.ofFun f := by
  simp [positionPot, hj]

theorem positionPot_ge (th Pn : LocPot X) (f : X → ℝ) {i : ℕ} {j : Fin e} (hj : ¬ (j : ℕ) < i) :
    positionPot th Pn f i j = Pn + LocPot.ofFun fun _ => 0 := by
  simp [positionPot, hj]

theorem add_ofFun_U (P : LocPot X) (u : X → ℝ) (x : X) :
    (P + LocPot.ofFun u).U x = P.U x ∩ Set.univ := rfl

theorem add_ofFun_φ (P : LocPot X) (u : X → ℝ) (x y : X) :
    (P + LocPot.ofFun u).φ x y = P.φ x y + u y := rfl

end Slots

section Vertical

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]

theorem sum_log_vertFactor_local (D : ComponentData II Ψ K J Ω W) (M : XModel D) (F : Finset ℕ)
    (hF : ∀ p ∈ F, p ∈ D.S) {U : Set M.Xc} (hU : IsOpen U) {s : M.Xc → (Σ k, J k) → ℂ}
    (hs : ∀ y ∈ U, s y ∈ mcPts (mCoordIdeal D.y)) (hh : ∀ p, M.atlas.HoloOn U fun y => s y p)
    {y₀ : M.Xc} (hy₀ : y₀ ∈ U) :
    ∃ U' : Set M.Xc, IsOpen U' ∧ y₀ ∈ U' ∧ U' ⊆ U ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U' G ∧
      ∀ y ∈ U', ∑ p ∈ F, Real.log (D.vertFactor p (s y)) = (G y).re := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    exact ⟨U, hU, hy₀, subset_rfl, fun _ => 0, fun j w _ => analyticAt_const, fun y _ => by simp⟩
  | insert p F hp ih =>
    obtain ⟨U₁, hU₁, hy₁, hs₁, G₁, hG₁, hre₁⟩ := ih fun q hq => hF q (Finset.mem_insert_of_mem hq)
    obtain ⟨T, hT, hT0, hev⟩ := GroundTheory.Heights₂.Heights.NineStatements.NbarLeviChartReg.vertFactor_local D
      (hF p (Finset.mem_insert_self p F)) (hs y₀ hy₀)
    obtain ⟨U₂, hU₂, hy₂, hs₂, hQ, G₂, hG₂, hre₂⟩ := log_norm_section_local M.atlas hU hh hy₀ hT hT0 hev
    refine ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hy₁, hy₂⟩, fun y hy => hs₁ hy.1, fun y => G₂ y + G₁ y, ?_, ?_⟩
    · intro j w hw
      exact (hG₂ j w ⟨hw.1, hw.2.2⟩).add (hG₁ j w ⟨hw.1, hw.2.1⟩)
    · intro y hy
      rw [Finset.sum_insert hp, hQ y hy.2 (hs y (hs₂ hy.2)), hre₂ y hy.2, hre₁ y hy.1, Complex.add_re]

end Vertical

theorem ptsIntegral_word_eq_mInt : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ) (Nb Bm : HermLine J) (Pn : ReciprocityTheory.AnForm.M.LocPot M.Xc) (i : ℕ) (f G₀ : M.Xc → ℝ) (g : ((Σ k, J k) → ℂ) → ℝ), ReciprocityTheory.AnForm.M.IsPotential M.atlas Pn → (∀ x, ∀ y₀ ∈ (Pn).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Pn).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, J k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Pn).φ x y' - (fun z => Real.log (Nb.h z)) (s y') = (G y').re) → M.atlas.SmoothOn S.R.Yo f → (∀ z ∈ mcPts (mCoordIdeal D.y), M.proj z ∈ S.R.Yo → Real.log (Bm.h z) = Real.log (S.ref.h z) + f (M.proj z) + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z)) → (∀ z ∈ mcPts (mCoordIdeal D.y), M.proj z ∈ S.R.Yo → g z = G₀ (M.proj z)) → (∀ j, MeasureTheory.AEStronglyMeasurable (G₀ ∘ (M.atlas.chart j).symm) (MeasureTheory.volume.restrict (M.atlas.chart j).target)) → ReciprocityTheory.AnForm.M.MIntegrable M.atlas (positionPot S.R.th Pn f i) G₀ → ptsIntegral (mCoordIdeal D.y) (pot fun j : Fin D.n => if (j : ℕ) < i then Bm else Nb) g = ReciprocityTheory.AnForm.M.mInt M.atlas (positionPot S.R.th Pn f i) G₀ := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M S B Nb Bm Pn i f G₀ g hPot hPn hf hBm hg hG₀ hInt
  obtain ⟨hYo, hnull, -, -⟩ := GlobalTheory.T.regular_chart_data_properties D.n M.Xc M.atlas S.R
  have hex : ∃ Q : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (D.n + 1) → ℂ), IsGoodProj (mCoordIdeal D.y) Q :=
    goodProjExists K J _ D.n D.arith
  have hnull' : ∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (S.R.Yoᶜ ∪ ∅)) = 0 := by
    intro j
    rw [Set.union_empty]
    exact hnull j
  have hN : IsPtsNull (mCoordIdeal D.y) D.n (∅ : Set ((Σ k, J k) → ℂ)) := fun _ _ => by simp
  have hsm : ∀ (j : Fin D.n) x, M.atlas.SmoothOn ((positionPot S.R.th Pn f i j).U x ∩ S.R.Yo)
      ((positionPot (e := D.n) S.R.th Pn f i j).φ x) := by
    intro j x a
    by_cases hj : (j : ℕ) < i
    · rw [positionPot_lt _ _ _ hj, add_ofFun_U]
      have s1 : (M.atlas.chart a).target ∩ (M.atlas.chart a).symm ⁻¹' ((S.R.th.U x ∩ Set.univ) ∩ S.R.Yo) ⊆
          (M.atlas.chart a).target ∩ (M.atlas.chart a).symm ⁻¹' S.R.th.U x := fun w hw => ⟨hw.1, hw.2.1.1⟩
      have s2 : (M.atlas.chart a).target ∩ (M.atlas.chart a).symm ⁻¹' ((S.R.th.U x ∩ Set.univ) ∩ S.R.Yo) ⊆
          (M.atlas.chart a).target ∩ (M.atlas.chart a).symm ⁻¹' S.R.Yo := fun w hw => ⟨hw.1, hw.2.2⟩
      exact ((S.R.th_pot.1 x a).mono s1).add ((hf a).mono s2)
    · rw [positionPot_ge _ _ _ hj, add_ofFun_U]
      have s1 : (M.atlas.chart a).target ∩ (M.atlas.chart a).symm ⁻¹' ((Pn.U x ∩ Set.univ) ∩ S.R.Yo) ⊆
          (M.atlas.chart a).target ∩ (M.atlas.chart a).symm ⁻¹' Pn.U x := fun w hw => ⟨hw.1, hw.2.1.1⟩
      exact ((hPot.1 x a).mono s1).add contDiffOn_const
  have hloc : ∀ (j : Fin D.n), ∀ x, ∀ y₀ ∈ (positionPot (e := D.n) S.R.th Pn f i j).U x ∩ S.R.Yo,
      ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (positionPot (e := D.n) S.R.th Pn f i j).U x ∩ S.R.Yo ∧
        ∃ s : M.Xc → (Σ k, J k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (s y') = y') ∧
          (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧
            ∀ y' ∈ U, (positionPot (e := D.n) S.R.th Pn f i j).φ x y' -
              (fun z => (1 : ℝ) * Real.log ((if (j : ℕ) < i then Bm else Nb).h z)) (s y') = (G y').re := by
    intro j x y₀ hy
    by_cases hj : (j : ℕ) < i
    · rw [positionPot_lt _ _ _ hj, add_ofFun_U] at hy
      rw [positionPot_lt _ _ _ hj, add_ofFun_U]
      simp only [if_pos hj, _root_.one_mul, add_ofFun_φ]
      obtain ⟨hyU, hyY⟩ := hy
      obtain ⟨U, hUo, hyU', hUs, s, hs, hh, G, hG, hre⟩ := S.th_ref x y₀ hyU.1
      obtain ⟨U₂, hU₂o, hy₂, hU₂s, G₂, hG₂, hre₂⟩ := sum_log_vertFactor_local D M (D.SB B)
        (fun p hp => (Finset.mem_filter.1 hp).1) (hUo.inter hYo) (s := s) (fun y hy => (hs y hy.1).1)
        (fun p => holoOn_mono _ (hh p) Set.inter_subset_left) ⟨hyU', hyY⟩
      refine ⟨U₂, hU₂o, hy₂, fun y hy => ⟨⟨hUs (hU₂s hy).1, trivial⟩, (hU₂s hy).2⟩, s,
        fun y hy => hs y (hU₂s hy).1, fun p => holoOn_mono _ (hh p) fun y hy => (hU₂s hy).1,
        fun y => G y - G₂ y, ?_, ?_⟩
      · intro a w hw
        exact (hG a w ⟨hw.1, (hU₂s hw.2).1⟩).sub (hG₂ a w hw)
      · intro y hy
        have hmem := hs y (hU₂s hy).1
        have hpY : M.proj (s y) ∈ S.R.Yo := by
          rw [hmem.2]
          exact (hU₂s hy).2
        have e1 := hBm (s y) hmem.1 hpY
        rw [hmem.2] at e1
        have e2 := hre y (hU₂s hy).1
        have e3 := hre₂ y hy
        rw [e1, Complex.sub_re]
        linarith
    · rw [positionPot_ge _ _ _ hj, add_ofFun_U] at hy
      rw [positionPot_ge _ _ _ hj, add_ofFun_U]
      simp only [if_neg hj, _root_.one_mul, add_ofFun_φ, add_zero]
      obtain ⟨hyU, hyY⟩ := hy
      obtain ⟨U, hUo, hyU', hUs, s, hs, hh, G, hG, hre⟩ := hPn x y₀ hyU
      exact ⟨U ∩ S.R.Yo, hUo.inter hYo, ⟨hyU', hyY⟩, fun y hy => ⟨hUs hy.1, hy.2⟩, s,
        fun y hy => hs y hy.1, fun p => holoOn_mono _ (hh p) Set.inter_subset_left, G,
        holoOn_mono _ hG Set.inter_subset_left, fun y hy => hre y hy.1⟩
  have hmain := GlobalTheory.T.mixed_integral_model_formula K J (mCoordIdeal D.y) D.n M hex.choose S.R.Yo ∅ ∅ (fun _ => 1)
    (fun j : Fin D.n => if (j : ℕ) < i then Bm else Nb) (positionPot S.R.th Pn f i) g G₀ D.arith hex.choose_spec
    hYo hnull' hN hsm hloc (fun z hz _ hY _ => hg z hz hY) hG₀
  have h := (hmain.2.2 hInt).2
  have hfun : (fun (j : Fin D.n) z => (1 : ℝ) * Real.log ((if (j : ℕ) < i then Bm else Nb).h z)) =
      pot fun j : Fin D.n => if (j : ℕ) < i then Bm else Nb := by
    funext j z
    simp [pot]
  unfold ptsIntegral
  rw [dif_pos hex, ← hfun]
  exact h

end GlobalTheory.CompanionTheory.Ar.Cusp
