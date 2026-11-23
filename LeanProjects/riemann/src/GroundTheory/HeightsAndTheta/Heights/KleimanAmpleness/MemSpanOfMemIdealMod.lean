import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Hyps
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.HypsTer
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.HypsBis
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.HypsAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver cechZc quotPart cechMap)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomogIdeal)

noncomputable section

section Charts

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [Algebra S Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {N : ℕ} {e : ι k₀ ≃ Fin (N + 1)}

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem mem_span_of_le {A B : Subalgebra S Ω} (h : A ≤ B) {s : Set Ω} {v : Ω}
    (hv : v ∈ Submodule.span A s) : v ∈ Submodule.span B s := by
  induction hv using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span hz
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul a z _ hz =>
    have := Submodule.smul_mem _ (⟨a, h a.2⟩ : B) hz
    rw [Subalgebra.smul_def] at this ⊢
    exact this

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem mul_mem_span {A : Subalgebra S Ω} {s : Set Ω} {a v : Ω} (ha : a ∈ A)
    (hv : v ∈ Submodule.span A s) : a * v ∈ Submodule.span A s := by
  have := Submodule.smul_mem _ (⟨a, ha⟩ : A) hv
  rwa [Subalgebra.smul_def] at this

theorem zpow_ratio_mem_overRing (d : ∀ k, ι k) (i : Fin (N + 1)) (n : ℤ) :
    (y ⟨k₀, d k₀⟩ / baseVec y k₀ e i) ^ n ∈ overRing (S := S) y k₀ e d i := by
  refine zpow_mem_of_inv_mem _ ?_ ?_ n
  · have : y ⟨k₀, d k₀⟩ / baseVec y k₀ e i = baseVec y k₀ e (e (d k₀)) / baseVec y k₀ e i := by
      simp [IndefiniteRowSideFullHecke.Kleiman2.blockVec]
    rw [this]
    exact chartRing_le_overRing d i (ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing _ i _)
  · rw [inv_div]
    exact chartRingOver_le_overRing d i (div_mem_chartRingOver d k₀ (e.symm i))

theorem mem_twist_single (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀) (β : K → ℤ) (c : ℤ) {i : Fin (N + 1)}
    (hi : baseVec y k₀ e i ≠ 0) (t : Ω) :
    t ∈ ((TranslateEq.ofSecond (bundleOfDeg (e := e) hy β)).twist (Kleiman.twistSys S (baseVec y k₀ e) c)).sub
        (Kleiman.singleChart hi) ↔
      ∀ d : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) →
        t * genInv y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) d ∈ overRing (S := S) y k₀ e d i := by
  rw [TranslateEq.mem_twist_twistSys_iff (TranslateEq.ofSecond (bundleOfDeg (e := e) hy β)).toSubSystem c
    (Kleiman.singleChart hi) (Finset.mem_singleton_self i)]
  constructor
  · rintro ⟨u, hu, rfl⟩ d hd
    have hu' : u ∈ latOf (S := S) y k₀ e β i := (ofSecond_sub_single (bundleOfDeg (e := e) hy β) hi u).1 hu
    have h1 := (mem_latOf β i u).1 hu' d hd
    rw [genInv_add_baseDeg β c hd]
    have heq : baseVec y k₀ e i ^ c • u * (genInv y β d * y ⟨k₀, d k₀⟩ ^ (-c)) =
        (y ⟨k₀, d k₀⟩ / baseVec y k₀ e i) ^ (-c) * (u * genInv y β d) := by
      have ha : baseVec y k₀ e i ^ c ≠ 0 := zpow_ne_zero c hi
      have hb : y ⟨k₀, d k₀⟩ ^ c ≠ 0 := zpow_ne_zero c (hd k₀)
      rw [smul_eq_mul, div_zpow]
      simp only [zpow_neg]
      field_simp
    rw [heq]
    exact mul_mem (zpow_ratio_mem_overRing d i (-c)) h1
  · intro h
    refine ⟨baseVec y k₀ e i ^ (-c) * t, ?_, ?_⟩
    · refine (ofSecond_sub_single (bundleOfDeg (e := e) hy β) hi _).2 ((mem_latOf β i _).2 fun d hd => ?_)
      have h1 := h d hd
      rw [genInv_add_baseDeg β c hd] at h1
      have heq : baseVec y k₀ e i ^ (-c) * t * genInv y β d =
          (y ⟨k₀, d k₀⟩ / baseVec y k₀ e i) ^ c * (t * (genInv y β d * y ⟨k₀, d k₀⟩ ^ (-c))) := by
        have ha : baseVec y k₀ e i ^ c ≠ 0 := zpow_ne_zero c hi
        have hb : y ⟨k₀, d k₀⟩ ^ c ≠ 0 := zpow_ne_zero c (hd k₀)
        rw [div_zpow, zpow_neg, zpow_neg]
        field_simp
      rw [heq]
      exact mul_mem (zpow_ratio_mem_overRing d i c) h1
    · rw [smul_eq_mul, ← mul_assoc, ← zpow_add₀ hi, add_neg_cancel, zpow_zero, one_mul]

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem aeval_ratio_monos {i : Fin (N + 1)} (hi : baseVec y k₀ e i ≠ 0) {s : Kleiman.Poly S N}
    (hs : s ∈ Kleiman.monos ({i} : Finset (Fin (N + 1)))) :
    aeval (fun j => baseVec y k₀ e j / baseVec y k₀ e i) s = 1 := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨j, hj, rfl⟩ := ha
    have hj' : j = i := by simpa using hj
    rw [hj', aeval_X, div_self hi]
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul, ha, hb, mul_one]

theorem mem_span_of_mem_idealMod {J : Ideal (MRingOver S ι)} {i : Fin (N + 1)} (hi : baseVec y k₀ e i ≠ 0)
    {q : Ω} (hq : q ∈ Kleiman.idealMod (x := baseVec y k₀ e) (satIdeal S y k₀ e J) (Kleiman.singleChart hi))
    {d : ∀ k, ι k} (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) :
    q ∈ Submodule.span (overRing (S := S) y k₀ e d i) (dehom S y J d) := by
  induction hq using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨f, s, n, hf, hs, hfn, hsn, rfl⟩ := hz
    have h1 := Kleiman.aeval_div_of_isHomogeneous (x := baseVec y k₀ e) hfn i
    have h2 := Kleiman.aeval_div_of_isHomogeneous (x := baseVec y k₀ e) hsn i
    rw [aeval_ratio_monos hi hs] at h2
    have hxn : baseVec y k₀ e i ^ n ≠ 0 := pow_ne_zero n hi
    have hf' : aeval (baseVec y k₀ e) f = baseVec y k₀ e i ^ n *
        aeval (fun j => baseVec y k₀ e j / baseVec y k₀ e i) f := by
      rw [h1]; field_simp
    have hs' : aeval (baseVec y k₀ e) s = baseVec y k₀ e i ^ n := by
      field_simp at h2; exact h2.symm
    rw [hf', hs', mul_div_cancel_left₀ _ hxn]
    exact aeval_mem_of_mem_satIdeal hf hi hd
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul a z _ hz =>
    rw [Kleiman.chartRing_smul_def]
    have ha : (a : Ω) ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i := by
      rw [TranslateEq.chartRing.equiv (S := S) (baseVec y k₀ e) hi]; exact a.2
    exact mul_mem_span (chartRing_le_overRing d i ha) hz

theorem mem_ideal_single (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀) (β : K → ℤ) (c : ℤ)
    {J : Ideal (MRingOver S ι)} {i : Fin (N + 1)} (hi : baseVec y k₀ e i ≠ 0) {u : Ω}
    (hu : u ∈ (((TranslateEq.ofSecond (bundleOfDeg (e := e) hy β)).twist (Kleiman.twistSys S (baseVec y k₀ e) c)).twist
      (Kleiman.idealSys (baseVec y k₀ e) (satIdeal S y k₀ e J))).sub (Kleiman.singleChart hi))
    {d : ∀ k, ι k} (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) :
    u * genInv y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) d ∈
      Submodule.span (overRing (S := S) y k₀ e d i) (dehom S y J d) := by
  induction hu using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨q, hq, a, ha, rfl⟩ := hz
    have ha' := (mem_twist_single hy β c hi a).1 ha d hd
    rw [smul_eq_mul, mul_assoc, mul_comm]
    exact mul_mem_span ha' (mem_span_of_mem_idealMod hi hq hd)
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | smul a z _ hz =>
    rw [Kleiman.chartRing_smul_def, mul_assoc]
    have ha : (a : Ω) ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i := by
      rw [TranslateEq.chartRing.equiv (S := S) (baseVec y k₀ e) hi]; exact a.2
    exact mul_mem_span (chartRing_le_overRing d i ha) hz

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem overRing_le_chart (d : ∀ k, ι k) (I : Kleiman.Chart (baseVec y k₀ e)) {i : Fin (N + 1)} (hi : i ∈ I.1) :
    overRing (S := S) y k₀ e d i ≤ chartRingOver S y d ⊔ Kleiman.chartRing S (baseVec y k₀ e) I := by
  refine sup_le le_sup_left (le_trans ?_ le_sup_right)
  refine Algebra.adjoin_le ?_
  rintro _ ⟨j, rfl⟩
  exact TranslateEq.div_mem_chartRing_of_mem I hi j

end Charts

theorem QuotSecsBase.proof (hV : QuotCocycleValues.Statement) (hL : QuotChartLift.Statement)
    (hI : QuotIdealSub.Statement) : QuotSecsBase.Statement := by
  intro S _ _ K _ _ ι _ _ Ω _ _ y k₀ N e J hJ hy _ β
  set x := baseVec y k₀ e with hx
  refine ⟨TranslateEq.ofSecond (bundleOfDeg (e := e) hy β), satIdeal S y k₀ e J,
    fun p hp n => homogeneousComponent_mem_satIdeal hp n, fun c z'' hz'' => ?_⟩
  have hγ : β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ = β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
    rw [natCast_zsmul]
  rw [hγ] at hz'' ⊢
  set γ := β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ with hγdef
  obtain ⟨w, hwa, hwb, hwc⟩ := hV S K ι Ω y J hJ γ z'' hz''
  have hlift := hL S K ι Ω y k₀ N e J γ w hy hwa hwb
  choose sf hsf using hlift
  have hpick : ∀ I : Kleiman.Chart x, ∃ i, i ∈ I.1 := fun I => I.2.1
  choose pick hpick using hpick
  have hxp : ∀ I : Kleiman.Chart x, x (pick I) ≠ 0 := fun I => (Kleiman.mem_support x).1 (I.2.2 (hpick I))
  have hsingle : ∀ {i} (hi : x i ≠ 0), pick (Kleiman.singleChart hi) = i := fun {i} hi => by
    simpa [Kleiman.singleChart] using hpick (Kleiman.singleChart hi)
  refine ⟨fun I => sf (pick I) (hxp I), fun I => ?_, fun I₁ I₂ h12 => ?_, fun t ht htI => ?_⟩
  ·
    have h1 := (mem_twist_single (S := S) hy β (c : ℤ) (hxp I) _).2 fun d hd => (hsf _ (hxp I) d hd).1
    refine SubSystem.mono _ (Kleiman.singleChart (hxp I)) I ?_ _ h1
    exact Finset.singleton_subset_iff.2 (hpick I)
  ·
    refine hI S K ι Ω y k₀ N e J hy β (c : ℤ) I₂ _ fun d hd => ?_
    have h1 := (hsf _ (hxp I₁) d hd).2
    have h2 := (hsf _ (hxp I₂) d hd).2
    have h1' := mem_span_of_le (overRing_le_chart d I₂ (h12 (hpick I₁))) h1
    have h2' := mem_span_of_le (overRing_le_chart d I₂ (hpick I₂)) h2
    have := sub_mem h1' h2'
    rw [← sub_mul, sub_sub_sub_cancel_right] at this
    exact this
  ·
    refine hwc t ?_ fun d hd => ?_
    ·
      simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
        Subalgebra.mem_toSubmodule]
      intro d hd
      have hi : x (e (d k₀)) ≠ 0 := by simpa [hx, IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hd k₀
      have h1 := (mem_twist_single (S := S) hy β (c : ℤ) hi t).1
        ((Submodule.mem_iInf _).1 ht (Kleiman.singleChart hi)) d hd
      rw [overRing_self] at h1
      exact h1
    · have hi : x (e (d k₀)) ≠ 0 := by simpa [hx, IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hd k₀
      have h1 := mem_ideal_single hy β (c : ℤ) hi (htI (Kleiman.singleChart hi)) hd
      have key : ∀ j (hj : x j ≠ 0), j = e (d k₀) → (sf j hj - w d) * genInv y γ d ∈
          Submodule.span (overRing (S := S) y k₀ e d (e (d k₀))) (dehom S y J d) := by
        intro j hj hj'
        subst hj'
        exact (hsf _ hj d hd).2
      have h2 := key _ (hxp (Kleiman.singleChart hi)) (hsingle hi)
      have h3 := add_mem h1 h2
      rw [← add_mul, sub_add_sub_cancel, overRing_self] at h3
      exact h3

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
