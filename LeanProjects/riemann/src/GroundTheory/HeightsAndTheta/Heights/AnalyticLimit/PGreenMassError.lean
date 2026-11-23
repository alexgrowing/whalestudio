import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureA
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassError
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.SystemIndependence
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.ConvergenceRate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot HoloMap mInt MIntegrable)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

namespace GreenMassError

section Forms

variable {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem formNonneg_of_posPot (A : FinHolAtlas e X) (V : Set X) (P : LocPot X) (hP : IsPosPot A P) :
    FormNonneg A V P := by
  intro x k y hy w
  by_cases hw : w = 0
  · subst hw
    rw [ReciprocityTheory.AnForm.levi_zero]
  · exact (hP x k y ⟨hy.1, hy.2.2⟩ w hw).le

theorem formNonneg_pullback (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (h : Y → X)
    (hh : HoloMap B A h) (V : Set X) (P : LocPot X) (hP : IsPotential A P)
    (hnn : FormNonneg A V P) : FormNonneg B (h ⁻¹' V) (P.pullback h hh.1) := by
  intro x k y hy w
  obtain ⟨hyt, hyV, hyU⟩ := hy
  obtain ⟨j, hj⟩ := A.cover (h ((B.chart k).symm y))
  have hτa : AnalyticAt ℂ (A.chart j ∘ h ∘ (B.chart k).symm) y := hh.2 k j y ⟨hyt, hj⟩
  have hτy : (A.chart j ∘ h ∘ (B.chart k).symm) y ∈ (A.chart j).target :=
    (A.chart j).map_source hj
  have hsymm : (A.chart j).symm ((A.chart j ∘ h ∘ (B.chart k).symm) y) = h ((B.chart k).symm y) :=
    (A.chart j).left_inv hj
  have hev : (P.pullback h hh.1).φ x ∘ (B.chart k).symm =ᶠ[𝓝 y]
      (P.φ (h x) ∘ (A.chart j).symm) ∘ (A.chart j ∘ h ∘ (B.chart k).symm) := by
    have hc : ContinuousAt (h ∘ (B.chart k).symm) y :=
      hh.1.continuousAt.comp ((B.chart k).continuousAt_symm hyt)
    filter_upwards [hc.preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)] with y' hy'
    simp only [Function.comp_apply, LocPot.pullback]
    rw [(A.chart j).left_inv (show h ((B.chart k).symm y') ∈ (A.chart j).source from hy')]
  have hU : (A.chart j).symm ((A.chart j ∘ h ∘ (B.chart k).symm) y) ∈ P.U (h x) := by
    rw [hsymm]
    exact hyU
  rw [ReciprocityTheory.AnForm.levi_congr hev w, ReciprocityTheory.AnForm.levi_comp w hτa
    (ReciprocityTheory.AnForm.M.pot_contDiffAt_two hP (h x) j hτy hU)]
  refine hnn (h x) j _ ⟨hτy, ?_, hU⟩ _
  show (A.chart j).symm ((A.chart j ∘ h ∘ (B.chart k).symm) y) ∈ V
  rw [hsymm]
  exact hyV

theorem smooth_comp_holoMap (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (h : Y → X)
    (hh : HoloMap B A h) {u : X → ℝ} (hu : A.Smooth u) : B.Smooth (u ∘ h) := by
  have hpot := ReciprocityTheory.AnForm.M.isPotentialPullback A B h hh _
    (ReciprocityTheory.AnForm.M.isPotential_ofFun A u hu)
  intro j y hy
  have := (hpot.1 ((B.chart j).symm y) j) y (by simpa [LocPot.pullback, LocPot.ofFun] using hy)
  simpa [LocPot.pullback, LocPot.ofFun, Function.comp_def] using this

theorem mInt_le_of_abs_le [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (V : Set X)
    (Φ : Fin e → LocPot X) (hpot : ∀ i, IsPotential A (Φ i)) (hnn : ∀ i, FormNonneg A V (Φ i))
    (hAn : A.IsAnalyticSubset Vᶜ) (hint : interior Vᶜ = ∅) {g f : X → ℝ}
    (hg : MIntegrable A Φ g) (hf : MIntegrable A Φ f) (K c : ℝ)
    (hle : ∀ x ∈ V, |g x| ≤ c * f x + K) :
    mInt A Φ g ≤ K * mInt A Φ (fun _ => 1) + c * mInt A Φ f := by
  have hK : MIntegrable A Φ (fun _ => K) :=
    ReciprocityTheory.AnForm.M.mIntegrableCont A Φ hpot _ continuous_const
  have h1 : MIntegrable A Φ (fun _ => (1 : ℝ)) :=
    ReciprocityTheory.AnForm.M.mIntegrableCont A Φ hpot _ continuous_const
  have hb := SystemIndependence.mIntegrable_linComb A Φ c hf hK
  have habs := SystemIndependence.abs_mInt_le A V Φ hpot hnn hAn hint hg hb hle
  have l1 := ReciprocityTheory.AnForm.M.mIntLinear A Φ hpot c f (fun _ => K) hf hK
  have l2 := ReciprocityTheory.AnForm.M.mIntLinear A Φ hpot K (fun _ => 1) (fun _ => 0) h1
    (SystemIndependence.mIntegrable_zero A Φ)
  beta_reduce at l1 l2
  rw [SystemIndependence.mInt_zero] at l2
  simp only [mul_one, add_zero] at l2
  rw [l1, l2] at habs
  linarith [le_abs_self (mInt A Φ g)]

end Forms

def nearBound (C t₀ : ℝ) : ℝ := t₀ ^ (1 / 3 : ℝ) + |errE C t₀| + |C| * |errE C t₀|

theorem tendsto_logPow_div (n : ℕ) :
    Tendsto (fun t => Real.log (ell t) ^ n / ell t) (𝓝[>] 0) (𝓝 0) := by
  have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero).comp tendsto_ell
  simpa [Function.comp_def] using this

theorem tendsto_nearBound (C : ℝ) : Tendsto (nearBound C) (𝓝[>] 0) (𝓝 0) := by
  have h13 : Tendsto (fun t : ℝ => t ^ (1 / 3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (1 / 3 : ℝ) (Or.inr (by norm_num))).tendsto
    rw [Real.zero_rpow (by norm_num)] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hE : Tendsto (fun t => errE C t) (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_logPow_div 1).const_mul C
    rw [mul_zero] at this
    refine this.congr fun t => ?_
    simp [errE, mul_div_assoc]
  have := (h13.add hE.abs).add (hE.abs.const_mul |C|)
  show Tendsto (fun t => t ^ (1 / 3 : ℝ) + |errE C t| + |C| * |errE C t|) _ _
  simpa using this

variable {D : ℕ} {W : Type} [TopologicalSpace W]

theorem one_le_exp_one : (1 : ℝ) ≤ Real.exp 1 := by
  have := Real.add_one_le_exp (1 : ℝ)
  linarith

theorem abs_gap_le (S : UIData D W) (a : ℕ) (ha : a < D + 1) {t₀ t : ℝ} (ht : 0 < t)
    (htt : t ≤ t₀) (h0 : S.ell₀ ≤ ell t₀) (he : Real.exp 1 ≤ ell t₀) {x : W} (hx : x ∈ S.Yo) :
    |S.gap a ha t₀ t x| ≤
      |S.C₁| * (tail S.Yo S.r (ell t₀)).indicator (fun y => Real.log (S.r y)) x +
        nearBound S.C t₀ := by
  have ht0 : 0 < t₀ := ht.trans_le htt
  have hell : ell t₀ ≤ ell t := Real.log_le_log (inv_pos.2 ht0) (inv_anti₀ ht htt)
  have h0t : S.ell₀ ≤ ell t := h0.trans hell
  have hmono := S.mono ⟨a, ha⟩ t t₀ ht htt h0 x
  have hgap : 0 ≤ S.gap a ha t₀ t x := by
    unfold UIData.gap
    linarith
  rw [abs_of_nonneg hgap]
  have hE := le_abs_self (errE S.C t₀)
  have hCE : S.C * errE S.C t₀ ≤ |S.C| * |errE S.C t₀| := by
    rw [← abs_mul]
    exact le_abs_self _
  have hr13 : 0 ≤ t₀ ^ (1 / 3 : ℝ) := Real.rpow_nonneg ht0.le _
  have hEa := abs_nonneg (errE S.C t₀)
  have hCa : 0 ≤ |S.C| * |errE S.C t₀| := by positivity
  have h1e := one_le_exp_one
  unfold nearBound
  by_cases hr : S.r x ≤ ell t₀
  · have hn := S.near ⟨a, ha⟩ t₀ ht0 h0 x hx hr
    have hl := S.lim_le ⟨a, ha⟩ t ht h0t x hx
    have hind : 0 ≤ |S.C₁| * (tail S.Yo S.r (ell t₀)).indicator (fun y => Real.log (S.r y)) x :=
      mul_nonneg (abs_nonneg _) (Set.indicator_nonneg (fun y hy => Real.log_nonneg (by
        have := hy.2
        linarith)) x)
    unfold UIData.gap
    linarith
  · replace hr := not_le.mp hr
    have hmem : x ∈ tail S.Yo S.r (ell t₀) := ⟨hx, hr.le⟩
    rw [Set.indicator_of_mem hmem]
    have hlog : 0 ≤ Real.log (S.r x) := Real.log_nonneg (by linarith)
    have h1 := (S.form ⟨a, ha⟩ t₀ ht0 h0).1.u_nonpos x hx
    have h2 := (S.form ⟨a, ha⟩ t ht h0t).1.le_u x hx
    have h3 : S.C₁ * Real.log (S.r x) ≤ |S.C₁| * Real.log (S.r x) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hlog
    unfold UIData.gap
    linarith

theorem isPotential_alt (S : UIData D W) {t : ℝ} (ht : 0 < t) (h0t : S.ell₀ ≤ ell t)
    (i : Fin (D + 1)) : IsPotential S.A (S.T t i) :=
  ReciprocityTheory.AnForm.M.isPotentialAdd S.A _ _ (S.form i t ht h0t).1.th_pot
    (ReciprocityTheory.AnForm.M.isPotential_ofFun S.A _ (S.form i t ht h0t).2)

theorem isPotential_mixed (S : UIData D W) {t : ℝ} (ht : 0 < t) (h0t : S.ell₀ ≤ ell t) (a : ℕ)
    (i : Fin (D + 1)) : IsPotential S.A (mixedForms S.Om.pot (S.T t) a i) := by
  unfold mixedForms
  split_ifs
  · exact isPotential_alt S ht h0t i
  · exact S.Om.isPot

theorem formNonneg_mixed (S : UIData D W) {t : ℝ} (ht : 0 < t) (h0t : S.ell₀ ≤ ell t) (a : ℕ)
    (i : Fin (D + 1)) : FormNonneg S.A S.Yo (mixedForms S.Om.pot (S.T t) a i) := by
  unfold mixedForms
  split_ifs
  · exact (S.form i t ht h0t).1.nonneg
  · exact formNonneg_of_posPot S.A S.Yo _ S.Om.pos

theorem mass_mixed [CompactSpace W] [T2Space W] (S : UIData D W) {t : ℝ} (ht : 0 < t)
    (h0t : S.ell₀ ≤ ell t) (a : ℕ) :
    mInt S.A (mixedForms S.Om.pot (S.T t) a) (fun _ => 1) =
      mInt S.A (mixedForms S.Om.pot S.th a) (fun _ => 1) := by
  have hpot : ∀ i, IsPotential S.A (mixedForms S.Om.pot S.th a i) := by
    intro i
    unfold mixedForms
    split_ifs
    · exact (S.form i t ht h0t).1.th_pot
    · exact S.Om.isPot
  have hsm : ∀ i, S.A.Smooth ((fun i : Fin (D + 1) => if (i : ℕ) < a then S.u i t else
      fun _ => (0 : ℝ)) i) := by
    intro i
    dsimp only
    split_ifs
    · exact (S.form i t ht h0t).2
    · exact fun _ => contDiffOn_const
  rw [← ReciprocityTheory.AnForm.M.massIndep S.A _ _ hpot hsm]
  apply ReciprocityTheory.AnForm.M.PLC.mInt_congr_phi
  intro i x y
  simp only [mixedForms, UIData.T, curForms, potForm]
  split_ifs <;> simp [locPot_add_φ, LocPot.ofFun]

theorem continuous_gap (S : UIData D W) (a : ℕ) (ha : a < D + 1) {t₀ t : ℝ} (ht : 0 < t)
    (htt : t ≤ t₀) (h0 : S.ell₀ ≤ ell t₀) : Continuous (S.gap a ha t₀ t) := by
  have ht0 : 0 < t₀ := ht.trans_le htt
  have h0t : S.ell₀ ≤ ell t :=
    h0.trans (Real.log_le_log (inv_pos.2 ht0) (inv_anti₀ ht htt))
  have c0 := ReciprocityTheory.AnForm.M.PLAux.smooth_continuous (S.form ⟨a, ha⟩ t₀ ht0 h0).2
  have c1 := ReciprocityTheory.AnForm.M.PLAux.smooth_continuous (S.form ⟨a, ha⟩ t ht h0t).2
  exact (c0.add continuous_const).sub c1

theorem errW_le [CompactSpace W] [T2Space W] (S : UIData D W) (a : ℕ) (ha : a < D + 1)
    {t₀ t : ℝ} (ht : 0 < t) (htt : t ≤ t₀) (h0 : S.ell₀ ≤ ell t₀) (he : Real.exp 1 ≤ ell t₀) :
    S.errW a ha t₀ t ≤ nearBound S.C t₀ * mInt S.A (mixedForms S.Om.pot S.th a) (fun _ => 1) +
      |S.C₁| * (|S.CE| * (Real.log (ell t₀) ^ (D + 1 + 1) / ell t₀)) := by
  have ht0 : 0 < t₀ := ht.trans_le htt
  have h0t : S.ell₀ ≤ ell t :=
    h0.trans (Real.log_le_log (inv_pos.2 ht0) (inv_anti₀ ht htt))
  have hpot := isPotential_mixed S ht h0t a
  have hg := ReciprocityTheory.AnForm.M.mIntegrableCont S.A _ hpot _ (continuous_gap S a ha ht htt h0)
  have htail := S.tail a (Nat.lt_succ_iff.mp ha) t ht h0t (ell t₀) he
  have key := mInt_le_of_abs_le S.A S.Yo _ hpot (formNonneg_mixed S ht h0t a) S.bd_analytic
    S.bd_interior hg htail.1 (nearBound S.C t₀) |S.C₁|
    (fun x hx => abs_gap_le S a ha ht htt h0 he hx)
  rw [mass_mixed S ht h0t a] at key
  have hℓ : 0 < ell t₀ := lt_of_lt_of_le (Real.exp_pos 1) he
  have hlog : 0 ≤ Real.log (ell t₀) := Real.log_nonneg (one_le_exp_one.trans he)
  have htb : mInt S.A (mixedForms S.Om.pot (S.T t) a)
      ((tail S.Yo S.r (ell t₀)).indicator fun x => Real.log (S.r x)) ≤
      |S.CE| * (Real.log (ell t₀) ^ (D + 1 + 1) / ell t₀) := by
    refine htail.2.trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (div_nonneg (pow_nonneg hlog _) hℓ.le)
  have := mul_le_mul_of_nonneg_left htb (abs_nonneg S.C₁)
  unfold UIData.errW
  linarith

theorem errDiv_le [CompactSpace W] [T2Space W] (S : UIData D W) (a : ℕ) (ha : a < D + 1)
    {t₀ t : ℝ} (ht : 0 < t) (htt : t ≤ t₀) (h0 : S.ell₀ ≤ ell t₀) (he : Real.exp 1 ≤ ell t₀) :
    S.errDiv a ha t₀ t ≤ ∑ k, (S.mult k : ℝ) * (nearBound S.C t₀ *
      mInt (S.B k) (restrictForms (S.comp k) (restForms S.Om.pot S.th a)) (fun _ => 1) +
        |S.C₁| * (|S.CE| * (Real.log (ell t₀) ^ (D + 1) / ell t₀))) := by
  have ht0 : 0 < t₀ := ht.trans_le htt
  have h0t : S.ell₀ ≤ ell t :=
    h0.trans (Real.log_le_log (inv_pos.2 ht0) (inv_anti₀ ht htt))
  unfold UIData.errDiv UIData.divInt
  refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have : CompactSpace (S.comp k) := isCompact_iff_compactSpace.mp
    (ReciprocityTheory.AnForm.M.sncClosed S.A S.L S.s S.mult S.comp S.s_snc k).isCompact
  have hholo := S.B_holo k
  have hpotW : ∀ i : Fin D, IsPotential S.A (restForms S.Om.pot (S.T t) a i) := by
    intro i
    unfold restForms
    split_ifs
    · exact isPotential_alt S ht h0t _
    · exact S.Om.isPot
  have hpot : ∀ i, IsPotential (S.B k) (restrictForms (S.comp k) (S.rest a t) i) := fun i =>
    ReciprocityTheory.AnForm.M.isPotentialPullback S.A (S.B k) Subtype.val hholo _ (hpotW i)
  have hnnW : ∀ i : Fin D, FormNonneg S.A S.Yo (restForms S.Om.pot (S.T t) a i) := by
    intro i
    unfold restForms
    split_ifs
    · exact (S.form _ t ht h0t).1.nonneg
    · exact formNonneg_of_posPot S.A S.Yo _ S.Om.pos
  have hnn : ∀ i, FormNonneg (S.B k) (Subtype.val ⁻¹' S.Yo)
      (restrictForms (S.comp k) (S.rest a t) i) := fun i =>
    formNonneg_pullback S.A (S.B k) Subtype.val hholo S.Yo _ (hpotW i) (hnnW i)
  have hg := ReciprocityTheory.AnForm.M.mIntegrableCont (S.B k) _ hpot _
    ((continuous_gap S a ha ht htt h0).comp continuous_subtype_val)
  have htail := S.tailComp k a (Nat.lt_succ_iff.mp ha) t ht h0t (ell t₀) he
  have key := mInt_le_of_abs_le (S.B k) (Subtype.val ⁻¹' S.Yo) _ hpot hnn (S.bdComp_analytic k)
    (S.bdComp_interior k) hg htail.1 (nearBound S.C t₀) |S.C₁| (fun z hz => by
      have hb := abs_gap_le S a ha ht htt h0 he hz
      have hind : (tail (Subtype.val ⁻¹' S.Yo) (S.r ∘ Subtype.val) (ell t₀)).indicator
          (fun x => Real.log ((S.r ∘ Subtype.val) x)) z =
          (tail S.Yo S.r (ell t₀)).indicator (fun y => Real.log (S.r y)) z.val := by
        rfl
      rw [hind]
      exact hb)
  have hmass : mInt (S.B k) (restrictForms (S.comp k) (S.rest a t)) (fun _ => 1) =
      mInt (S.B k) (restrictForms (S.comp k) (restForms S.Om.pot S.th a)) (fun _ => 1) := by
    have hpotθ : ∀ i, IsPotential (S.B k)
        (restrictForms (S.comp k) (restForms S.Om.pot S.th a) i) := by
      intro i
      refine ReciprocityTheory.AnForm.M.isPotentialPullback S.A (S.B k) Subtype.val hholo _ ?_
      unfold restForms
      split_ifs
      · exact (S.form _ t ht h0t).1.th_pot
      · exact S.Om.isPot
    have hsm : ∀ i, (S.B k).Smooth ((fun i : Fin D => if (i : ℕ) < a then
        S.u i.castSucc t ∘ Subtype.val else fun _ => (0 : ℝ)) i) := by
      intro i
      dsimp only
      split_ifs
      · exact smooth_comp_holoMap S.A (S.B k) Subtype.val hholo (S.form _ t ht h0t).2
      · exact fun _ => contDiffOn_const
    rw [← ReciprocityTheory.AnForm.M.massIndep (S.B k) _ _ hpotθ hsm]
    apply ReciprocityTheory.AnForm.M.PLC.mInt_congr_phi
    intro i x y
    simp only [restrictForms, restForms, UIData.rest, UIData.T, curForms, potForm]
    split_ifs <;> simp [locPot_add_φ, LocPot.ofFun, LocPot.pullback]
  rw [hmass] at key
  have hℓ : 0 < ell t₀ := lt_of_lt_of_le (Real.exp_pos 1) he
  have hlog : 0 ≤ Real.log (ell t₀) := Real.log_nonneg (one_le_exp_one.trans he)
  have htb := htail.2.trans (show S.CE * Real.log (ell t₀) ^ (D + 1) / ell t₀ ≤
      |S.CE| * (Real.log (ell t₀) ^ (D + 1) / ell t₀) by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (div_nonneg (pow_nonneg hlog _) hℓ.le))
  have := mul_le_mul_of_nonneg_left htb (abs_nonneg S.C₁)
  unfold UIData.rest UIData.T at key ⊢
  linarith

end GreenMassError

theorem GreenMassError.proof : GreenMassError.Statement := by
  intro D W _ _ _ S a ha δ hδ
  have hK := GreenMassError.tendsto_nearBound S.C
  have hL := GreenMassError.tendsto_logPow_div
  have hW : Tendsto (fun t₀ => GreenMassError.nearBound S.C t₀ *
      mInt S.A (mixedForms S.Om.pot S.th a) (fun _ => 1) +
      |S.C₁| * (|S.CE| * (Real.log (ell t₀) ^ (D + 1 + 1) / ell t₀))) (𝓝[>] 0) (𝓝 0) := by
    have := (hK.mul_const (mInt S.A (mixedForms S.Om.pot S.th a) (fun _ => 1))).add
      (((hL (D + 1 + 1)).const_mul |S.CE|).const_mul |S.C₁|)
    simpa using this
  have hDv : Tendsto (fun t₀ => ∑ k, (S.mult k : ℝ) * (GreenMassError.nearBound S.C t₀ *
      mInt (S.B k) (restrictForms (S.comp k) (restForms S.Om.pot S.th a)) (fun _ => 1) +
        |S.C₁| * (|S.CE| * (Real.log (ell t₀) ^ (D + 1) / ell t₀)))) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_finsetSum Finset.univ fun k _ =>
      ((hK.mul_const (mInt (S.B k) (restrictForms (S.comp k) (restForms S.Om.pot S.th a))
        (fun _ => 1))).add (((hL (D + 1)).const_mul |S.CE|).const_mul |S.C₁|)).const_mul
        (S.mult k : ℝ)
    simpa using this
  have hev := (hW.eventually (gt_mem_nhds hδ)).and ((hDv.eventually (gt_mem_nhds hδ)).and
    (tendsto_ell.eventually_ge_atTop (Real.exp 1)))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨u / 2, by linarith, fun t₀ t ht htt hτ h0 => ?_⟩
  have hmem : t₀ ∈ Set.Ioo 0 u := ⟨ht.trans_le htt, by linarith⟩
  obtain ⟨h1, h2, he⟩ := hsub hmem
  exact ⟨(GreenMassError.errW_le S a ha ht htt h0 he).trans h1.le,
    (GreenMassError.errDiv_le S a ha ht htt h0 he).trans h2.le⟩

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
