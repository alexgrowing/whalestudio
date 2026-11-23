import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StDivisorNull
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StProductBounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)

noncomputable section

namespace SystemIndependence

section Integrals

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem mIntegrable_linComb (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) (c : ℝ) {f f' : X → ℝ}
    (hf : MIntegrable A Φ f) (hf' : MIntegrable A Φ f') :
    MIntegrable A Φ (fun x => c * f x + f' x) := fun j K hK hKc =>
  IntegrableOn.congr_fun (((hf j K hK hKc).const_mul c).add (hf' j K hK hKc))
    (fun y _ => by simp only [Pi.add_apply]; ring) hKc.measurableSet

theorem mIntegrable_const_mul (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) (c : ℝ) {f : X → ℝ}
    (hf : MIntegrable A Φ f) : MIntegrable A Φ (fun x => c * f x) := fun j K hK hKc =>
  IntegrableOn.congr_fun ((hf j K hK hKc).const_mul c) (fun y _ => by beta_reduce; ring)
    hKc.measurableSet

theorem mIntegrable_zero (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) :
    MIntegrable A Φ (fun _ => 0) := fun j K _ _ => by
  simp

theorem mInt_zero (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) : mInt A Φ (fun _ => 0) = 0 := by
  unfold mInt ReciprocityTheory.AnForm.M.integralWith
  split_ifs <;> simp

theorem mInt_nonneg_on (A : FinHolAtlas D X) (V : Set X) (Φ : Fin D → LocPot X)
    (hpot : ∀ i, IsPotential A (Φ i)) (hnn : ∀ i, FormNonneg A V (Φ i)) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hf0 : ∀ x ∉ V, f x = 0) : 0 ≤ mInt A Φ f := by
  unfold mInt
  split_ifs with h
  · unfold ReciprocityTheory.AnForm.M.integralWith
    refine Finset.sum_nonneg fun j _ =>
      setIntegral_nonneg (A.chart j).open_target.measurableSet fun y hy => ?_
    by_cases hyV : (A.chart j).symm y ∈ V
    · have hd : 0 ≤ ReciprocityTheory.AnForm.M.locDens A Φ j y :=
        ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ y fun i =>
          ReciprocityTheory.AnForm.M.hessC_posSemidef_of_levi _ y
            (ReciprocityTheory.AnForm.M.pot_contDiffAt_two (hpot i) _ j hy ((Φ i).mem_U _))
            (fun w => hnn i _ j y ⟨hy, hyV, (Φ i).mem_U _⟩ w)
      exact mul_nonneg (mul_nonneg (h.some.nonneg j _) (hf _)) hd
    · rw [hf0 _ hyV]
      simp
  · exact le_rfl

theorem abs_mInt_le [CompactSpace X] [T2Space X] (A : FinHolAtlas D X) (V : Set X)
    (Φ : Fin D → LocPot X) (hpot : ∀ i, IsPotential A (Φ i)) (hnn : ∀ i, FormNonneg A V (Φ i))
    (hAn : A.IsAnalyticSubset Vᶜ) (hint : interior Vᶜ = ∅) {h b : X → ℝ}
    (hh : MIntegrable A Φ h) (hb : MIntegrable A Φ b) (hle : ∀ x ∈ V, |h x| ≤ b x) :
    |mInt A Φ h| ≤ mInt A Φ b := by
  have key : ∀ c : ℝ, |c| = 1 → 0 ≤ mInt A Φ (fun x => c * h x + b x) := by
    intro c hc
    have hcongr := ReciprocityTheory.AnForm.M.mIntCongrNull A Φ Vᶜ hAn hint (fun x => c * h x + b x)
      (V.indicator fun x => c * h x + b x) (fun x hx => by
        rw [Set.indicator_of_mem (Set.not_notMem.mp hx)])
    rw [hcongr]
    refine mInt_nonneg_on A V Φ hpot hnn _ (fun x => ?_) (fun x hx => Set.indicator_of_notMem hx _)
    by_cases hx : x ∈ V
    · rw [Set.indicator_of_mem hx]
      have h1 := hle x hx
      have h2 : |c * h x| = |h x| := by rw [abs_mul, hc, one_mul]
      have h3 := neg_abs_le (c * h x)
      linarith
    · rw [Set.indicator_of_notMem hx]
  have l1 := ReciprocityTheory.AnForm.M.mIntLinear A Φ hpot (-1) h b hh hb
  have l2 := ReciprocityTheory.AnForm.M.mIntLinear A Φ hpot 1 h b hh hb
  have k1 := key (-1) (by norm_num)
  have k2 := key 1 (by norm_num)
  rw [abs_le]
  constructor <;> linarith

end Integrals

end SystemIndependence

def SystemIndependence.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (R R' : RegChartData A) (S : System R) (S' : System R') (g : X → ℝ) (B : ℝ),
    R'.Yo = R.Yo → A.Smooth g → (∀ x ∈ R.Yo, R.φ x = R'.φ x + g x) →
    (∀ x ∈ R.Yo, |R.r x - R'.r x| ≤ B) →
    ∀ (Om : KaehlerForm A) (C₁ : ℝ) (th : ℝ → Fin D → LocPot X) (u : ℝ → Fin D → X → ℝ),
    (∀ t, 0 < t → ∀ i, IsSmoothPotForm A R.Yo R.r Om C₁ (th t i) (u t i)) →
    Tendsto (fun t => mInt A (fun i => potForm (th t i) (u t i))
      (fun x => S.ph t x - S'.ph t x - g x)) (𝓝[>] 0) (𝓝 0)

theorem SystemIndependence.bound (hN : DivisorNull.Statement) (hE : ProductBounds.Statement)
    {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (R R' : RegChartData A) (S : System R) (S' : System R') (g : X → ℝ) (B : ℝ)
    (hYo : R'.Yo = R.Yo) (hg : A.Smooth g) (hφ : ∀ x ∈ R.Yo, R.φ x = R'.φ x + g x)
    (hr : ∀ x ∈ R.Yo, |R.r x - R'.r x| ≤ B) (Om : KaehlerForm A) (C₁ : ℝ)
    (th : ℝ → Fin D → LocPot X) (u : ℝ → Fin D → X → ℝ)
    (hT : ∀ t, 0 < t → ∀ i, IsSmoothPotForm A R.Yo R.r Om C₁ (th t i) (u t i)) :
    ∃ V CE K : ℝ, 0 ≤ K ∧ ∀ t, 0 < t → S.ell₀ ≤ ell t → S'.ell₀ ≤ ell t → 1 ≤ ell t →
      Real.exp 1 + B ≤ ell t →
      |mInt A (fun i => potForm (th t i) (u t i)) (fun x => S.ph t x - S'.ph t x - g x)| ≤
        (2 * t ^ (1 / 3 : ℝ) + errE |S.C| t + errE |S'.C| t) * V +
          K * (CE * Real.log (ell t - B) ^ (D + 1) / (ell t - B)) := by
  obtain ⟨V, CE, hVC⟩ := hE A R Om C₁
  obtain ⟨hAn, hint⟩ := hN A R
  have hlogB : 0 ≤ Real.log (1 + |B|) := Real.log_nonneg (by linarith [abs_nonneg B])
  set K := |S.C| + |R.C| + |S'.C| + |R'.C| * (1 + Real.log (1 + |B|)) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨V, CE, K, hK0, fun t ht h1 h2 h3 h4 => ?_⟩
  set ε := 2 * t ^ (1 / 3 : ℝ) + errE |S.C| t + errE |S'.C| t with hε
  set R₀ := ell t - B with hR₀
  have hR₀e : Real.exp 1 ≤ R₀ := by linarith
  obtain ⟨⟨hMi, hMeq, hMle⟩, hTl⟩ := hVC (th t) (u t) (hT t ht)
  obtain ⟨hTi, hTle⟩ := hTl R₀ hR₀e
  have hpot : ∀ i, IsPotential A (potForm (th t i) (u t i)) := fun i =>
    ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ (hT t ht i).1.th_pot
      (ReciprocityTheory.AnForm.M.isPotential_ofFun A _ (hT t ht i).2)
  have hnn : ∀ i, FormNonneg A R.Yo (potForm (th t i) (u t i)) := fun i => (hT t ht i).1.nonneg
  have hcont : Continuous fun x => S.ph t x - S'.ph t x - g x :=
    ((ReciprocityTheory.AnForm.M.PLAux.smooth_continuous (S.smooth t ht h1)).sub
      (ReciprocityTheory.AnForm.M.PLAux.smooth_continuous (S'.smooth t ht h2))).sub
      (ReciprocityTheory.AnForm.M.PLAux.smooth_continuous hg)
  have hhI := ReciprocityTheory.AnForm.M.mIntegrableCont A _ hpot _ hcont

  have hL : 0 ≤ Real.log (ell t) / ell t := div_nonneg (Real.log_nonneg h3) (by linarith)
  have herr : ∀ c : ℝ, errE c t ≤ errE |c| t ∧ 0 ≤ errE |c| t := fun c => by
    unfold errE
    rw [mul_div_assoc, mul_div_assoc]
    exact ⟨mul_le_mul_of_nonneg_right (le_abs_self c) hL, mul_nonneg (abs_nonneg c) hL⟩
  have ht3 : 0 ≤ t ^ (1 / 3 : ℝ) := Real.rpow_nonneg ht.le _
  have hε0 : 0 ≤ ε := by linarith [(herr S.C).2, (herr S'.C).2]

  have hpt : ∀ x ∈ R.Yo, |S.ph t x - S'.ph t x - g x| ≤
      ε * R.Yo.indicator 1 x + K * (tail R.Yo R.r R₀).indicator (fun x => Real.log (R.r x)) x := by
    intro x hx
    have hx' : x ∈ R'.Yo := hYo ▸ hx
    have ha0 := S.le_ph t ht h1 x hx
    have hb0 := S'.le_ph t ht h2 x hx'
    have hrx := abs_le.mp (hr x hx)
    have hr1 := R.one_le_r x hx
    have hr1' := R'.one_le_r x hx'
    have heq : S.ph t x - S'.ph t x - g x = (S.ph t x - R.φ x) - (S'.ph t x - R'.φ x) := by
      rw [hφ x hx]; ring
    rw [heq, Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    have hab : |(S.ph t x - R.φ x) - (S'.ph t x - R'.φ x)| ≤
        (S.ph t x - R.φ x) + (S'.ph t x - R'.φ x) := by
      rw [abs_le]; constructor <;> linarith
    have htl0 : 0 ≤ K * (tail R.Yo R.r R₀).indicator (fun x => Real.log (R.r x)) x :=
      mul_nonneg hK0 (Set.indicator_nonneg (fun y hy => Real.log_nonneg (R.one_le_r y hy.1)) x)
    by_cases hfar : R₀ ≤ R.r x
    · rw [Set.indicator_of_mem (show x ∈ tail R.Yo R.r R₀ from ⟨hx, hfar⟩)]
      have hlr : 1 ≤ Real.log (R.r x) := by
        rw [Real.le_log_iff_exp_le (by linarith)]
        linarith
      have hr' : R'.r x ≤ R.r x * (1 + |B|) := by
        nlinarith [le_abs_self B, abs_nonneg B]
      have hlog' : Real.log (R'.r x) ≤ Real.log (R.r x) + Real.log (1 + |B|) := by
        rw [← Real.log_mul (by linarith) (by linarith [abs_nonneg B])]
        exact Real.log_le_log (by linarith) hr'
      have hlog'0 : 0 ≤ Real.log (R'.r x) := Real.log_nonneg hr1'
      have ha : S.ph t x - R.φ x ≤ (|S.C| + |R.C|) * Real.log (R.r x) := by
        have e1 := S.ph_le t ht h1 x
        have e2 := R.le_φ x hx
        have e3 : R.C * Real.log (R.r x) ≤ |R.C| * Real.log (R.r x) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
        have e4 : |S.C| ≤ |S.C| * Real.log (R.r x) := le_mul_of_one_le_right (abs_nonneg _) hlr
        linarith [le_abs_self S.C]
      have hb : S'.ph t x - R'.φ x ≤
          (|S'.C| + |R'.C| * (1 + Real.log (1 + |B|))) * Real.log (R.r x) := by
        have e1 := S'.ph_le t ht h2 x
        have e2 := R'.le_φ x hx'
        have e3 : R'.C * Real.log (R'.r x) ≤ |R'.C| * Real.log (R'.r x) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hlog'0
        have e4 : |R'.C| * Real.log (R'.r x) ≤
            |R'.C| * (Real.log (R.r x) + Real.log (1 + |B|)) :=
          mul_le_mul_of_nonneg_left hlog' (abs_nonneg _)
        have e5 : Real.log (1 + |B|) ≤ Real.log (1 + |B|) * Real.log (R.r x) :=
          le_mul_of_one_le_right hlogB hlr
        have e6 : |R'.C| * Real.log (1 + |B|) ≤ |R'.C| * (Real.log (1 + |B|) * Real.log (R.r x)) :=
          mul_le_mul_of_nonneg_left e5 (abs_nonneg _)
        have e7 : |S'.C| ≤ |S'.C| * Real.log (R.r x) := le_mul_of_one_le_right (abs_nonneg _) hlr
        nlinarith [le_abs_self S'.C]
      have hsum : (|S.C| + |R.C|) * Real.log (R.r x) +
          (|S'.C| + |R'.C| * (1 + Real.log (1 + |B|))) * Real.log (R.r x) = K * Real.log (R.r x) := by
        rw [hK]; ring
      linarith
    · have hnear : R.r x ≤ ell t := by linarith
      have hnear' : R'.r x ≤ ell t := by linarith
      have ha := S.near t ht h1 x hx hnear
      have hb := S'.near t ht h2 x hx' hnear'
      linarith [(herr S.C).1, (herr S'.C).1]

  have hbI : MIntegrable A (fun i => potForm (th t i) (u t i)) (fun x => ε * R.Yo.indicator 1 x +
      K * (tail R.Yo R.r R₀).indicator (fun x => Real.log (R.r x)) x) :=
    mIntegrable_linComb A _ ε hMi (mIntegrable_const_mul A _ K hTi)
  have hmain := abs_mInt_le A R.Yo _ hpot hnn hAn hint hhI hbI hpt
  have l1 := ReciprocityTheory.AnForm.M.mIntLinear A _ hpot ε (R.Yo.indicator 1)
    (fun x => K * (tail R.Yo R.r R₀).indicator (fun x => Real.log (R.r x)) x) hMi
    (mIntegrable_const_mul A _ K hTi)
  have l2 := ReciprocityTheory.AnForm.M.mIntLinear A _ hpot K
    ((tail R.Yo R.r R₀).indicator (fun x => Real.log (R.r x))) (fun _ => 0) hTi
    (mIntegrable_zero A _)
  simp only [add_zero, mInt_zero] at l2
  have hm0 : 0 ≤ mInt A (fun i => potForm (th t i) (u t i)) (R.Yo.indicator 1) :=
    mInt_nonneg_on A R.Yo _ hpot hnn _
      (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
      (fun x hx => Set.indicator_of_notMem hx _)
  have hmV : mInt A (fun i => potForm (th t i) (u t i)) (R.Yo.indicator 1) ≤ V := hMeq.trans_le hMle
  have step1 := mul_le_mul_of_nonneg_left hmV hε0
  have step2 := mul_le_mul_of_nonneg_left hTle hK0
  rw [l1, l2] at hmain
  linarith

theorem SystemIndependence.proof (hN : DivisorNull.Statement) (hE : ProductBounds.Statement) :
    SystemIndependence.Statement := by
  intro D X _ _ _ A R R' S S' g B hYo hg hφ hr Om C₁ th u hT
  obtain ⟨V, CE, K, _, hbd⟩ :=
    SystemIndependence.bound hN hE A R R' S S' g B hYo hg hφ hr Om C₁ th u hT
  have hell : Tendsto ell (𝓝[>] 0) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have hlog : ∀ n : ℕ, Tendsto (fun y : ℝ => Real.log y ^ n / y) atTop (𝓝 0) := fun n => by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero
  have herr : ∀ c : ℝ, Tendsto (fun t => errE c t) (𝓝[>] 0) (𝓝 0) := fun c => by
    have h := ((hlog 1).comp hell).const_mul c
    rw [mul_zero] at h
    refine h.congr fun t => ?_
    simp [errE, Function.comp, mul_div_assoc]
  have hrp : Tendsto (fun t : ℝ => t ^ (1 / 3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 (1 / 3 : ℝ) (Or.inr (by norm_num))).tendsto
    rw [Real.zero_rpow (by norm_num)] at h
    exact h.mono_left nhdsWithin_le_nhds
  have htail : Tendsto (fun t => CE * Real.log (ell t - B) ^ (D + 1) / (ell t - B))
      (𝓝[>] 0) (𝓝 0) := by
    have h := ((hlog (D + 1)).comp (tendsto_atTop_add_const_right _ (-B) hell)).const_mul CE
    rw [mul_zero] at h
    refine h.congr fun t => ?_
    simp [Function.comp, sub_eq_add_neg, mul_div_assoc]
  have hlim : Tendsto (fun t => (2 * t ^ (1 / 3 : ℝ) + errE |S.C| t + errE |S'.C| t) * V +
      K * (CE * Real.log (ell t - B) ^ (D + 1) / (ell t - B))) (𝓝[>] 0) (𝓝 0) := by
    have h := ((((hrp.const_mul 2).add (herr |S.C|)).add (herr |S'.C|)).mul_const V).add
      (htail.const_mul K)
    simpa using h
  refine squeeze_zero_norm' ?_ hlim
  have ev : ∀ L : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), L ≤ ell t := fun L => hell.eventually_ge_atTop L
  filter_upwards [self_mem_nhdsWithin, ev S.ell₀, ev S'.ell₀, ev 1, ev (Real.exp 1 + B)] with
    t ht h1 h2 h3 h4
  rw [Real.norm_eq_abs]
  exact hbd t ht h1 h2 h3 h4

section Inhabitant

open ReciprocityTheory.AnForm.M (p1)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitant

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
