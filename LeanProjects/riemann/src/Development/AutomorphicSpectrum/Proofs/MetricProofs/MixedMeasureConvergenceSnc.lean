import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.UnifInt
import ReciprocityTheory.AnalyticForms.LeviForms.TailBound
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UIObjects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassZero
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FixedMemberBase
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CompChartEventuallyEq
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BdryIsAnalyticSubsetInteriorEmpty
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformRestrictionStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformEnergyBoundOfSectionStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights.AnalyticLimit (UIData KaehlerForm TailLogBound greenEp secNorm potForm
  mixedForms restForms restrictForms curForms IsSmoothPotForm IsBoundedPotForm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

section Helpers

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem levi_rsmul_eq (A : FinHolAtlas e X) (Θ : LocPot X) (hΘ : IsPotential A Θ) (c : ℝ) (x : X)
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target)
    (h : (A.chart j).symm y ∈ Θ.U x) (w : Fin e → ℂ) :
    levi ((Θ.rsmul c).φ x ∘ (A.chart j).symm) y w = c * levi (Θ.φ x ∘ (A.chart j).symm) y w := by
  have hC := potential_contDiffAt_chart hΘ x j hy h
  exact TailChernBound.levi_smul' c hC w

theorem isPosPot_rsmul (A : FinHolAtlas e X) (Θ : LocPot X) (hΘ : IsPotential A Θ)
    (hpos : IsPosPot A Θ) {c : ℝ} (hc : 0 < c) : IsPosPot A (Θ.rsmul c) := by
  intro x j y hy w hw
  rw [levi_rsmul_eq A Θ hΘ c x j hy.1 hy.2]
  exact mul_pos hc (hpos x j y hy w hw)

theorem levi_le_of_psh (A : FinHolAtlas e X) (Θ P : LocPot X) (hΘ : IsPotential A Θ)
    (hP : IsPotential A P) (K : ℝ) (h : IsPsh A (Θ.rsmul K + P.rsmul (-1))) (x : X) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (h1 : (A.chart j).symm y ∈ Θ.U x)
    (h2 : (A.chart j).symm y ∈ P.U x) (w : Fin e → ℂ) :
    levi (P.φ x ∘ (A.chart j).symm) y w ≤ K * levi (Θ.φ x ∘ (A.chart j).symm) y w := by
  have c1 := potential_contDiffAt_chart hΘ x j hy h1
  have c2 := potential_contDiffAt_chart hP x j hy h2
  have h0 : 0 ≤ levi (fun z => K * (Θ.φ x ∘ (A.chart j).symm) z +
      (-1) * (P.φ x ∘ (A.chart j).symm) z) y w := h x j y ⟨hy, ⟨h1, h2⟩⟩ w
  rw [TailChernBound.levi_lin K (-1) c1 c2 w] at h0
  linarith

theorem isPsh_congr (A : FinHolAtlas e X) {P Q : LocPot X} (hU : ∀ x, Q.U x ⊆ P.U x)
    (hφ : ∀ x z, Q.φ x z = P.φ x z) (h : IsPsh A P) : IsPsh A Q := by
  intro x j y hy w
  have e1 : Q.φ x = P.φ x := funext (hφ x)
  rw [e1]
  exact h x j y ⟨hy.1, hU x hy.2⟩ w

theorem isSection_pull {e' : ℕ} {X' : Type} [TopologicalSpace X'] {A : FinHolAtlas e X}
    {A' : FinHolAtlas e' X'} {h : X' → X} (hh : HoloMap A' A h) {L : LocPot X} {s : X → X → ℂ}
    (hs : IsSection A L s) :
    IsSection A' (L.pullback h hh.1) (fun x y => s (h x) (h y)) := by
  refine ⟨fun x j t ht => ?_, fun x x' y hy => hs.2 _ _ _ hy⟩
  obtain ⟨k, hk⟩ := A.cover (h ((A'.chart j).symm t))
  obtain ⟨hz, hs'⟩ := chart_image_mem (A := A) (A' := A') (h := h) j k hk
  have hzU : (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) t) ∈ L.U (h x) := by
    rw [hs']; exact ht.2
  have h1 : AnalyticAt ℂ (s (h x) ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (A'.chart j).symm) t) :=
    hs.1 (h x) k _ ⟨hz, hzU⟩
  have h2 := hh.2 j k t ⟨ht.1, hk⟩
  have h3 := h1.comp h2
  refine h3.congr ?_
  filter_upwards [holoMap_preimage_mem_nhds hh j k ht.1 hk] with t' ht'
  simp only [Function.comp_apply, (A.chart k).left_inv ht'.2]

theorem hessC_sub_const {D : ℕ} (F : (Fin D → ℂ) → ℝ) (c : ℝ) (z : Fin D → ℂ) :
    hessC (fun y => F y - c) z = hessC F z := by
  have h : fderiv ℝ (fun y => F y - c) = fderiv ℝ F := by
    funext y
    exact fderiv_sub_const ..
  unfold hessC
  rw [h]

theorem locDens_sub_const (A : FinHolAtlas e X) (Φ Φ' : Fin e → LocPot X) (c : Fin e → ℝ)
    (h : ∀ i x z, (Φ' i).φ x z = (Φ i).φ x z - c i) (j : Fin A.n) (y : Fin e → ℂ) :
    locDens A Φ' j y = locDens A Φ j y := by
  unfold locDens maDens
  have : (fun k => hessC (fun y' => (Φ' k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) =
      fun k => hessC (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
    funext k
    simp only [h]
    exact hessC_sub_const _ _ _
  rw [this]

theorem mInt_sub_const (A : FinHolAtlas e X) (Φ Φ' : Fin e → LocPot X) (c : Fin e → ℝ)
    (h : ∀ i x z, (Φ' i).φ x z = (Φ i).φ x z - c i) (g : X → ℝ) :
    mInt A Φ' g = mInt A Φ g := by
  have : locDens A Φ' = locDens A Φ := by
    funext j y
    exact locDens_sub_const A Φ Φ' c h j y
  unfold mInt
  simp only [integralWith, this]

theorem tailLogBound_mono (A : FinHolAtlas e X) (Yo : Set X) (r : X → ℝ) (T : Fin e → LocPot X)
    {c c' : ℝ} (hc : c ≤ c') (h : TailLogBound A Yo r T c) : TailLogBound A Yo r T c' := by
  intro R hR
  obtain ⟨h1, h2⟩ := h R hR
  refine ⟨h1, h2.trans ?_⟩
  have hR0 : 0 < R := (Real.exp_pos 1).trans_le hR
  have hl : 0 ≤ Real.log R := Real.log_nonneg ((Real.one_le_exp zero_le_one).trans hR)
  gcongr

theorem ell_eq (t : ℝ) : ell t = Real.log (1 / t) := by
  simp [ell]

theorem errE_eq (C t : ℝ) : errE C t = epsT C t := by
  simp [errE, epsT, ell]

theorem le_of_ell_le {t₁ t : ℝ} (ht₁ : 0 < t₁) (ht : 0 < t) (h : Real.log (1 / t₁) ≤ ell t) :
    t ≤ t₁ := by
  rw [ell_eq] at h
  by_contra hc
  have h1 : 1 / t < 1 / t₁ := one_div_lt_one_div_of_lt ht₁ (not_le.1 hc)
  have := Real.log_lt_log (by positivity) h1
  linarith

theorem ell_le_of_le {t₁ t : ℝ} (ht : 0 < t) (h : t ≤ t₁) : Real.log (1 / t₁) ≤ ell t := by
  rw [ell_eq]
  exact Real.log_le_log (one_div_pos.2 (ht.trans_le h)) (one_div_le_one_div_of_le ht h)

end Helpers

section Tail

theorem tail_mixed (hTB : TailBoundStatement) {n : ℕ} {Y : Type} [TopologicalSpace Y]
    [CompactSpace Y] [T2Space Y] (A : FinHolAtlas n Y) (L : LocPot Y) (s : Y → Y → ℂ) {r : ℕ}
    (m : Fin r → ℕ) (W : Fin r → Set Y) (hL : IsPotential A L) (hs : IsSection A L s)
    (hsnc : IsSNC A L s m W) (hnorm : ∀ y, logNormSec L s y ≤ 0) (P : Fin n → LocPot Y)
    (Om : LocPot Y) (hP : ∀ i, IsPotential A (P i)) (hPp : ∀ i, IsPosPot A (P i))
    (hOm : IsPotential A Om) (hOmp : IsPosPot A Om) (C₁ : ℝ) (hC₁ : 0 ≤ C₁) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ b : ℕ, b ≤ n → ∀ (uu : Fin n → Y → ℝ) (T : Fin n → LocPot Y),
      (∀ i, A.Smooth (uu i)) → (∀ i, IsPsh A (P i + LocPot.ofFun (uu i))) →
      (∀ i, ∀ y ∉ bdry s, -C₁ * Real.log (rW L s y) ≤ uu i y ∧ uu i y ≤ 0) →
      (∀ i : Fin n, (i : ℕ) < b → ∀ x y, (T i).φ x y = (P i).φ x y + uu i y) →
      (∀ i : Fin n, ¬ (i : ℕ) < b → ∀ x y, (T i).φ x y = Om.φ x y) →
      TailLogBound A (bdry s)ᶜ (rW L s) T CE := by
  classical
  have h : ∀ b : ℕ, _ := fun b : ℕ =>
    GlobalTheory.T.uniform_energy_bound_of_section hTB A (fun i : Fin n => if (i : ℕ) < b then P i else Om) L s m W C₁
      (fun i => by split_ifs; exacts [hP i, hOm])
      (fun i => by split_ifs; exacts [hPp i, hOmp]) hL hs hsnc hnorm hC₁
  choose CE hCE0 hCE using h
  refine ⟨∑ b ∈ Finset.range (n + 1), CE b, Finset.sum_nonneg fun i _ => hCE0 i,
    fun b hb uu T hu hpsh hbd h1 h2 => ?_⟩
  refine tailLogBound_mono _ _ _ _
    (Finset.single_le_sum (f := CE) (fun i _ => hCE0 i) (Finset.mem_range.2 (by omega)))
    (hCE b (fun i => if (i : ℕ) < b then uu i else fun _ => 0) T ?_ ?_ ?_ ?_)
  · intro i
    split_ifs
    · exact hu i
    · exact fun _ => contDiffOn_const
  · intro i
    split_ifs
    · exact hpsh i
    · exact isPsh_congr A (P := Om) (fun x z hz => hz.1) (fun x z => add_zero _)
        (TailBoundAlt.isPsh_of_isPosPot A _ hOmp)
  · intro i y hy
    split_ifs
    · exact hbd i y hy
    · have hlog : 0 ≤ Real.log (rW L s y) :=
        Real.log_nonneg ((Real.one_le_exp zero_le_one).trans (rW_ge L s hnorm y))
      have : -C₁ * Real.log (rW L s y) ≤ 0 := by nlinarith
      exact ⟨this, le_rfl⟩
  · intro i x y
    by_cases hi : (i : ℕ) < b
    · simp only [hi, if_true]
      exact h1 i hi x y
    · simp only [hi, if_false, add_zero]
      exact h2 i hi x y

end Tail

section Green

theorem green_integrable {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (L' : LocPot X) (v : X → X → ℂ)
    {r : ℕ} (m : Fin r → ℕ) (W : Fin r → Set X) (hL' : IsPotential A L') (hv : IsSection A L' v)
    (hsnc : IsSNC A L' v m W) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (hψ : ∀ i, IsPsh A (Φ i)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (greenEp L' v ε) (maMeasure A Φ) ∧
      ∫ y, greenEp L' v ε y ∂maMeasure A Φ = mInt A Φ (greenEp L' v ε) := by
  obtain ⟨_, hμ⟩ := maMeasure_thm A Φ hΦ hψ
  have hN : Continuous (secNorm L' v) :=
    GroundTheory.Heights₂.Heights.AnalyticLimit.continuous_secNorm A L' v hL' hv
  have hmeas : Measurable (greenEp L' v ε) :=
    ((hN.measurable.pow_const 2).const_div ε |>.const_add 1).log
  have hlogN : Integrable (logNormSec L' v) (maMeasure A Φ) :=
    ((hμ _ hN.measurable.log).1).1 (logNormIntegrable A L' v m W hL' hv hsnc Φ hΦ)
  have hc : Continuous fun x => Real.log (secNorm L' v x ^ 2 + 1) :=
    ((hN.pow 2).add continuous_const).log fun x =>
      (by positivity : (0 : ℝ) < secNorm L' v x ^ 2 + 1).ne'
  have hh : Integrable (fun x => Real.log (secNorm L' v x ^ 2 + 1)) (maMeasure A Φ) :=
    ((hμ _ hc.measurable).1).1 (mIntegrableCont A Φ hΦ _ hc)
  have hG1 : Integrable (greenEp L' v 1) (maMeasure A Φ) := by
    rw [show greenEp L' v 1 = fun x =>
        Real.log (secNorm L' v x ^ 2 + 1) - 2 * logNormSec L' v x from
      funext (GroundTheory.Heights₂.Heights.AnalyticLimit.greenEp_one_eq L' v)]
    exact hh.sub (hlogN.const_mul 2)
  have hint : Integrable (greenEp L' v ε) (maMeasure A Φ) :=
    hG1.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (GroundTheory.Heights₂.Heights.AnalyticLimit.greenEp_nonneg L' v hε.le x)]
      exact GroundTheory.Heights₂.Heights.AnalyticLimit.greenEp_le_one L' v hε.le hε1 x)
  exact ⟨hint, ((hμ _ hmeas).2 (((hμ _ hmeas).1).2 hint)).symm⟩

end Green

section Core

theorem isPosPot_pull_of_half {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']
    {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X} (hh : HoloMap A' A h)
    (Θ P : LocPot X) (hΘ : IsPotential A Θ) (hP : IsPotential A P)
    (hΘ' : IsPosPot A' (Θ.pullback h hh.1)) (hsub : ∀ x, P.U x ⊆ Θ.U x)
    (hpsh : IsPsh A (P + Θ.rsmul (-(1 / 2)))) : IsPosPot A' (P.pullback h hh.1) := by
  have hQ : IsPotential A (P + Θ.rsmul (-(1 / 2))) :=
    isPotentialAdd A _ _ hP (isPotentialRsmul A _ _ hΘ)
  have hQ' := isPotentialPullback A A' h hh _ hQ
  have hΘp := isPotentialPullback A A' h hh _ hΘ
  have hQpsh := isPsh_pull hh hQ hpsh
  refine isPosPot_of_lt A' (Θ.pullback h hh.1) ((P + Θ.rsmul (-(1 / 2))).pullback h hh.1)
    (fun _ => 0) hΘp hΘ' hQ' (fun _ => contDiffOn_const) 0 (1 / 2) (by norm_num) ?_ _ ?_ ?_
  · refine isPsh_congr A' (P := (P + Θ.rsmul (-(1 / 2))).pullback h hh.1)
      (fun x z hz => hz.1.1) (fun x z => ?_) hQpsh
    show _ + 0 + 0 * _ = _
    ring
  · intro x z hz
    exact ⟨⟨hz, hsub _ hz⟩, hsub _ hz⟩
  · intro x z
    show P.φ (h x) (h z) = (P.φ (h x) (h z) + -(1 / 2) * Θ.φ (h x) (h z)) + 0 +
      1 / 2 * Θ.φ (h x) (h z)
    ring

theorem green_small_core (hUI : GroundTheory.Heights₂.Heights.AnalyticLimit.UniformIntegrability.Statement)
    (hTB : TailBoundStatement) {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ)
    (W : Fin n → Set X) (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ) (hL : IsPotential A L)
    (hs : IsSection A L s) (hsnc : IsSNC A L s m W) (hnorm : ∀ y, logNormSec L s y ≤ 0)
    (L' : LocPot X) (v : X → X → ℂ) (Dg : Set X) (hL' : IsPotential A L') (hv : IsSection A L' v)
    (hsncv : IsSNC A L' v ![1] ![Dg])
    (hsncsv : IsSNC A (L + L') (fun x y => s x y * v x y) (Fin.snoc m 1) (Fin.snoc W Dg))
    (thS : Fin (e + 1) → LocPot X) (uS : Fin (e + 1) → ℝ → X → ℝ) (limS : Fin (e + 1) → X → ℝ)
    (Cc C₁ t₁ : ℝ) (hC₁ : 0 ≤ C₁) (ht₁ : 0 < t₁)
    (hpot : ∀ a, IsPotential A (thS a)) (hposS : ∀ a, IsPosPot A (thS a))
    (hhalf : ∀ a, IsPsh A (thS a + Θ.rsmul (-(1 / 2)))) (hsub : ∀ a x, (thS a).U x ⊆ Θ.U x)
    (hfam : ∀ a t, 0 < t → t ≤ t₁ → A.Smooth (uS a t) ∧ IsPsh A (thS a + LocPot.ofFun (uS a t)) ∧
      (∀ y, uS a t y ≤ 0) ∧ ∀ y ∉ bdry s, -C₁ * Real.log (rW L s y) ≤ uS a t y)
    (hlim : ∀ a t, 0 < t → t ≤ t₁ → ∀ y ∉ bdry s, limS a y ≤ uS a t y)
    (hnear : ∀ a t, 0 < t → t ≤ t₁ → ∀ y ∉ bdry s, rW L s y ≤ ell t →
      uS a t y ≤ limS a y + t ^ (1 / 3 : ℝ) + errE Cc t)
    (hmono : ∀ a t t', 0 < t → t ≤ t' → t' ≤ t₁ → ∀ y, uS a t y ≤ uS a t' y + Cc * errE Cc t')
    (η : ℝ) (hη : 0 < η) :
    ∃ ε₀ t₃ : ℝ, 0 < ε₀ ∧ 0 < t₃ ∧ t₃ ≤ t₁ ∧ ∀ ε t : ℝ, 0 < ε → ε ≤ ε₀ → 0 < t → t ≤ t₃ →
      mInt A (fun i => potForm (thS i) (uS i t)) (greenEp L' v ε) ≤ η := by
  classical
  obtain ⟨B, hB, n', m', W', hΘB, hposB, hsncB⟩ :=
    GlobalTheory.T.uniform_restriction_statement_holds A Θ L s m W hΘ hpos hL hs L' v Dg hL' hv hsncv hsncsv
  haveI : CompactSpace Dg := isCompact_iff_compactSpace.mp
    (show IsClosed Dg from SimpleNormalCrossingSliceCharts.isClosed_divisorComponent A L' v ![1] ![Dg] hsncv 0).isCompact
  have hLB : IsPotential B (L.pullback Subtype.val hB.1) := isPotentialPullback A B _ hB L hL
  have hsB : IsSection B (L.pullback Subtype.val hB.1) (fun x y => s x.1 y.1) :=
    isSection_pull hB hs
  have hK := fun a => tail_chern_bound A Θ (thS a) hΘ hpos (hpot a)
  choose K hK0 hK1 hK2 using hK
  obtain ⟨Kt, hKt⟩ : ∃ Kt : ℝ, Kt = ∑ a, K a + 1 := ⟨_, rfl⟩
  have hKpos : 0 < Kt := by
    have : 0 ≤ ∑ a, K a := Finset.sum_nonneg fun a _ => hK0 a
    linarith
  have hKa : ∀ a, K a ≤ Kt := fun a => by
    have : K a ≤ ∑ a, K a :=
      Finset.single_le_sum (f := K) (fun i _ => hK0 i) (Finset.mem_univ a)
    linarith
  let Om : KaehlerForm A := ⟨Θ.rsmul Kt, isPotentialRsmul A Kt Θ hΘ,
    isPosPot_rsmul A Θ hΘ hpos hKpos⟩
  have hOmB : IsPosPot B (Om.pot.pullback Subtype.val hB.1) :=
    isPosPot_rsmul B _ hΘB hposB hKpos
  obtain ⟨CE₁, hCE₁, hT₁⟩ := tail_mixed hTB A L s m W hL hs hsnc hnorm thS Om.pot hpot hposS
    Om.isPot Om.pos C₁ hC₁
  obtain ⟨CE₂, hCE₂, hT₂⟩ := tail_mixed hTB B (L.pullback Subtype.val hB.1)
    (fun x y => s x.1 y.1) m' W' hLB hsB hsncB (fun y => hnorm y.1)
    (fun i => (thS i.castSucc).pullback Subtype.val hB.1) (Om.pot.pullback Subtype.val hB.1)
    (fun i => isPotentialPullback A B _ hB _ (hpot _))
    (fun i => isPosPot_pull_of_half hB Θ _ hΘ (hpot _) hposB (hsub _) (hhalf _))
    (isPotentialPullback A B _ hB _ Om.isPot) hOmB C₁ hC₁
  have hBd := bdry_isAnalyticSubset_interior_empty A L s m W hs hsnc
  have hBdB := bdry_isAnalyticSubset_interior_empty B _ _ m' W' hsB hsncB
  have hYo : IsOpen (bdry s)ᶜ := (LeviFormBoundaryTopology.isClosed_bdry hs).isOpen_compl
  have hsnc1 : IsSNC A L' v (fun _ : Fin 1 => 1) (fun _ : Fin 1 => Dg) := by
    have e1 : (fun _ : Fin 1 => (1 : ℕ)) = ![1] := by
      funext k
      fin_cases k
      rfl
    have e2 : (fun _ : Fin 1 => Dg) = ![Dg] := by
      funext k
      fin_cases k
      rfl
    rw [e1, e2]
    exact hsncv
  have e3 : (Subtype.val ⁻¹' (bdry s)ᶜ : Set Dg)ᶜ = bdry (fun x y : Dg => s x.1 y.1) := by
    ext y
    simp [bdry]
  have hform : ∀ a t, 0 < t → Real.log (1 / t₁) ≤ ell t →
      IsSmoothPotForm A (bdry s)ᶜ (rW L s) Om C₁ (thS a) (uS a t) := by
    intro a t ht hl
    obtain ⟨hsm, hpshu, hle0, hlow⟩ := hfam a t ht (le_of_ell_le ht₁ ht hl)
    have hΘpsh := TailBoundAlt.isPsh_of_isPosPot A _ hpos
    have hSpsh := TailBoundAlt.isPsh_of_isPosPot A _ (hposS a)
    refine ⟨⟨hpot a, ?_, ?_, fun j => (hsm j).mono fun y hy => ⟨hy.1, trivial⟩,
      fun x _ => hle0 x, fun x hx => ?_, fun x k y hy w => hpshu x k y ⟨hy.1, hy.2.2⟩ w,
      Or.inl hsm⟩, hsm⟩
    · intro x k y hy w
      have hyΘ : (A.chart k).symm y ∈ Θ.U x := hy.2.2
      have h1 := levi_le_of_psh A Θ (thS a) hΘ (hpot a) (K a) (hK2 a) x k hy.1 hyΘ hy.2.1.2 w
      have h2 := hΘpsh x k y ⟨hy.1, hyΘ⟩ w
      show 1 * _ ≤ 1 * levi ((Θ.rsmul Kt).φ x ∘ (A.chart k).symm) y w
      rw [levi_rsmul_eq A Θ hΘ Kt x k hy.1 hyΘ, one_mul, one_mul]
      exact h1.trans (mul_le_mul_of_nonneg_right (hKa a) h2)
    · intro x k y hy w
      have hyΘ : (A.chart k).symm y ∈ Θ.U x := hy.2.1.2
      have h2 := hΘpsh x k y ⟨hy.1, hyΘ⟩ w
      have h3 := hSpsh x k y ⟨hy.1, hy.2.2⟩ w
      show -1 * levi ((Θ.rsmul Kt).φ x ∘ (A.chart k).symm) y w ≤ 1 * _
      rw [levi_rsmul_eq A Θ hΘ Kt x k hy.1 hyΘ]
      nlinarith [mul_nonneg hKpos.le h2]
    · have := hlow x hx
      linarith
  let S : UIData e X :=
    { A := A
      Om := Om
      L := L'
      s := v
      nc := 1
      mult := fun _ => 1
      comp := fun _ => Dg
      B := fun _ => B
      L_pot := hL'
      s_sec := hv
      s_snc := hsnc1
      B_holo := fun _ => hB
      Yo := (bdry s)ᶜ
      Yo_open := hYo
      bd_analytic := by rw [compl_compl]; exact hBd.1
      bd_interior := by rw [compl_compl]; exact hBd.2
      bdComp_analytic := fun _ => by rw [e3]; exact hBdB.1
      bdComp_interior := fun _ => by rw [e3]; exact hBdB.2
      r := rW L s
      th := thS
      u := uS
      lim := limS
      C := Cc
      C₁ := C₁
      ell₀ := Real.log (1 / t₁)
      CE := CE₁ + CE₂
      form := hform
      lim_le := fun a t ht hl x hx => hlim a t ht (le_of_ell_le ht₁ ht hl) x hx
      near := fun a t ht hl x hx hr => hnear a t ht (le_of_ell_le ht₁ ht hl) x hx hr
      mono := fun a t t' ht htt hl x =>
        hmono a t t' ht htt (le_of_ell_le ht₁ (ht.trans_le htt) hl) x
      tail := fun b hb t ht hl => by
        have htt := le_of_ell_le ht₁ ht hl
        refine tailLogBound_mono _ _ _ _ (by linarith : CE₁ ≤ CE₁ + CE₂)
          (hT₁ b (by omega) (fun i => uS i t) _ (fun i => (hfam i t ht htt).1)
            (fun i => (hfam i t ht htt).2.1)
            (fun i y hy => ⟨(hfam i t ht htt).2.2.2 y hy, (hfam i t ht htt).2.2.1 y⟩) ?_ ?_)
        · intro i hi x y
          have : mixedForms Om.pot (curForms thS uS t) b i = curForms thS uS t i := if_pos hi
          rw [this]
          rfl
        · intro i hi x y
          have : mixedForms Om.pot (curForms thS uS t) b i = Om.pot := if_neg hi
          rw [this]
      tailComp := fun k b hb t ht hl => by
        have htt := le_of_ell_le ht₁ ht hl
        refine tailLogBound_mono _ _ _ _ (by linarith : CE₂ ≤ CE₁ + CE₂)
          (hT₂ b hb (fun i => uS i.castSucc t ∘ Subtype.val) _
            (fun i => smoothOn_pull hB isOpen_univ (hfam _ t ht htt).1)
            (fun i => ?_)
            (fun i y hy => ⟨(hfam _ t ht htt).2.2.2 y.1 hy, (hfam _ t ht htt).2.2.1 y.1⟩) ?_ ?_)
        · refine isPsh_congr B
            (P := (thS i.castSucc + LocPot.ofFun (uS i.castSucc t)).pullback Subtype.val hB.1)
            (fun x z hz => ⟨hz.1, trivial⟩) (fun x z => rfl)
            (isPsh_pull hB (isPotentialAdd A _ _ (hpot _)
              (isPotential_ofFun A _ (hfam _ t ht htt).1)) (hfam _ t ht htt).2.1)
        · intro i hi x y
          have : restForms Om.pot (curForms thS uS t) b i = curForms thS uS t i.castSucc :=
            if_pos hi
          show (restForms Om.pot (curForms thS uS t) b i).φ x.1 y.1 = _
          rw [this]
          rfl
        · intro i hi x y
          have : restForms Om.pot (curForms thS uS t) b i = Om.pot := if_neg hi
          show (restForms Om.pot (curForms thS uS t) b i).φ x.1 y.1 = _
          rw [this]
          rfl }
  obtain ⟨ε₀, hε₀, t₃, ht₃, h⟩ := hUI S η hη
  refine ⟨ε₀, min t₃ t₁, hε₀, lt_min ht₃ ht₁, min_le_right _ _, fun ε t hε hεle ht htle => ?_⟩
  exact h ε t hε hεle ht (htle.trans (min_le_left _ _))
    (ell_le_of_le ht (htle.trans (min_le_right _ _)))

end Core

theorem green_small_uniform : GroundTheory.Heights₂.Heights.AnalyticLimit.UniformIntegrability.Statement → TailBoundStatement → ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas (e + 1) X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (L' : LocPot X) (v : X → X → ℂ) (Dg : Set X), IsPotential A L' → IsSection A L' v → IsSNC A L' v ![1] ![Dg] → IsSNC A (L + L') (fun x y => s x y * v x y) (Fin.snoc m 1) (Fin.snoc W Dg) → ∀ (th : Fin (e + 1) → LocPot X) (ph : Fin (e + 1) → X → ℝ) (phT : Fin (e + 1) → ℝ → X → ℝ) (C₅ C t₀ : ℝ), (∀ i, IsSingWeight A L s (th i) (ph i) C₅) → (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) → ∀ η : ℝ, 0 < η → ∃ ε₀ t₁ : ℝ, 0 < ε₀ ∧ 0 < t₁ ∧ ∀ ε t : ℝ, 0 < ε → ε ≤ ε₀ → 0 < t → t ≤ t₁ → Integrable (GroundTheory.Heights₂.Heights.AnalyticLimit.greenEp L' v ε) (maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ)) ∧ ∫ y, GroundTheory.Heights₂.Heights.AnalyticLimit.greenEp L' v ε y ∂maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ) ≤ η := by
  intro hUI hTB e X _ _ _ _ _ A Θ L s n m W hΘ hpos hL hs hsnc hnorm L' v Dg hL' hv hsncv hsncsv
    th ph phT C₅ C t₀ hWt hR η hη
  have hbase := fun i => fixedMember_base A Θ L s (th i) (ph i) (phT i) C₅ C t₀ hΘ hpos hnorm
    (hWt i) (hR i)
  choose t₂ ht₂ ht₂0 hb using hbase
  obtain ⟨t₁, ht₁, hle⟩ : ∃ t₁ : ℝ, 0 < t₁ ∧ ∀ i, t₁ ≤ t₂ i :=
    ⟨Finset.univ.inf' Finset.univ_nonempty t₂, (Finset.lt_inf'_iff _).2 fun i _ => ht₂ i,
      fun i => Finset.inf'_le _ (Finset.mem_univ i)⟩
  have hB1 := fun i => hb i t₁ ht₁ (hle i)
  have hle₀ : ∀ i t, t ≤ t₁ → t ≤ t₀ := fun i t h => h.trans ((hle i).trans (ht₂0 i))
  obtain ⟨ε₀, t₃, hε₀, ht₃, ht₃₁, hmain⟩ := green_small_core hUI hTB A Θ L s m W hΘ hpos hL hs hsnc
    hnorm L' v Dg hL' hv hsncv hsncsv (fun a => th a + LocPot.ofFun (phT a t₁) + Θ)
    (fun a t y => phT a t y - phT a t₁ y - C * epsT C t₁)
    (fun a y => ph a y - phT a t₁ y - C * epsT C t₁) C (|C₅| + |C| + 1) t₁
    (by positivity) ht₁ (fun a => (hB1 a).1) (fun a => (hB1 a).2.2.1) (fun a => (hB1 a).2.1)
    (fun a x z hz => hz.2) (fun a t ht htt => (hB1 a).2.2.2 t ht htt)
    (fun a t ht htt y hy => by
      obtain ⟨-, -, h3, -⟩ := (hR a).2.2 t ht (hle₀ a t htt)
      have := h3 y hy
      linarith)
    (fun a t ht htt y hy hr => by
      obtain ⟨-, -, -, -, -, h6, -⟩ := (hR a).2.2 t ht (hle₀ a t htt)
      have := h6 y hy (by rw [← ell_eq]; exact hr)
      rw [errE_eq]
      linarith)
    (fun a t t' ht htt htt' y => by
      obtain ⟨-, -, -, -, -, -, -, h8⟩ := (hR a).2.2 t ht (hle₀ a t (htt.trans htt'))
      have := h8 t' htt (hle₀ a t' htt') y
      rw [errE_eq]
      linarith)
    η hη
  refine ⟨min ε₀ 1, t₃, lt_min hε₀ one_pos, ht₃, fun ε t hε hεle ht htle => ?_⟩
  have htt₁ : t ≤ t₁ := htle.trans ht₃₁
  have hΦ := fun i => hb i t ht (htt₁.trans (hle i))
  obtain ⟨hint, heq⟩ := green_integrable A L' v ![1] ![Dg] hL' hv hsncv
    (fun i => th i + LocPot.ofFun (phT i t) + Θ) (fun i => (hΦ i).1)
    (fun i => TailBoundAlt.isPsh_of_isPosPot A _ (hΦ i).2.2.1) hε (hεle.trans (min_le_right _ _))
  refine ⟨hint, ?_⟩
  rw [heq, ← mInt_sub_const A _ (fun i => potForm (th i + LocPot.ofFun (phT i t₁) + Θ)
    (fun y => phT i t y - phT i t₁ y - C * epsT C t₁)) (fun _ => C * epsT C t₁) (fun i x z => ?_)]
  · exact hmain ε t hε (hεle.trans (min_le_left _ _)) ht htle
  · show (th i).φ x z + phT i t₁ z + Θ.φ x z + (phT i t z - phT i t₁ z - C * epsT C t₁) =
      (th i).φ x z + phT i t z + Θ.φ x z - C * epsT C t₁
    ring

end GlobalTheory.CompanionTheory.Ar.Giv
