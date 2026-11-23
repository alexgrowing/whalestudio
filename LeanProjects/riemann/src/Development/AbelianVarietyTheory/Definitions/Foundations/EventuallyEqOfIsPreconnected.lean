import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentConstEqOfTendsto

noncomputable section

namespace GlobalTheory.Cont

open Filter Topology Set GlobalTheory.ThetaInner

def rightOf (σ : ℝ) : Set ℂ := {s | σ < s.re}

def IsRightDomain (U : Set ℂ) : Prop := (∃ σ, rightOf σ ⊆ U) ∧ ∀ s ∈ U, ∀ t : ℝ, 0 ≤ t → s + t ∈ U

def EqRight (H h : ℂ → ℂ) : Prop := ∃ σ, EqOn H h (rightOf σ)

variable {σ τ : ℝ} {U U' : Set ℂ} {h h' H H' : ℂ → ℂ} {s s₀ c c' : ℂ} {n : ℤ} {k : ℕ}

@[simp] theorem mem_rightOf : s ∈ rightOf σ ↔ σ < s.re := by exact Iff.rfl

theorem isOpen_rightOf (σ : ℝ) : IsOpen (rightOf σ) := isOpen_lt continuous_const Complex.continuous_re

theorem rightOf_subset (e : σ ≤ τ) : rightOf τ ⊆ rightOf σ := fun _ hs => lt_of_le_of_lt e hs

theorem isRightDomain_univ : IsRightDomain univ := ⟨⟨0, subset_univ _⟩, fun _ _ _ _ => mem_univ _⟩

theorem isRightDomain_rightOf (σ : ℝ) : IsRightDomain (rightOf σ) := by
  refine ⟨⟨σ, subset_rfl⟩, fun s hs t ht => ?_⟩
  simp only [mem_rightOf, Complex.add_re, Complex.ofReal_re] at hs ⊢
  linarith

theorem isRightDomain_re_ge (σ : ℝ) : IsRightDomain {s | σ ≤ s.re} := by
  refine ⟨⟨σ, fun s hs => ?_⟩, fun s hs t ht => ?_⟩
  · simp only [mem_rightOf] at hs
    exact le_of_lt hs
  · show σ ≤ (s + t).re
    have hs' : σ ≤ s.re := hs
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith

theorem IsRightDomain.inter (a : IsRightDomain U) (b : IsRightDomain U') : IsRightDomain (U ∩ U') := by
  obtain ⟨⟨σ₁, h₁⟩, a₂⟩ := a
  obtain ⟨⟨σ₂, h₂⟩, b₂⟩ := b
  exact ⟨⟨max σ₁ σ₂, fun s hs => ⟨h₁ (rightOf_subset (le_max_left _ _) hs),
    h₂ (rightOf_subset (le_max_right _ _) hs)⟩⟩, fun s hs t ht => ⟨a₂ s hs.1 t ht, b₂ s hs.2 t ht⟩⟩

theorem IsRightDomain.preimage_add (a : IsRightDomain U) (z : ℂ) : IsRightDomain ((· + z) ⁻¹' U) := by
  obtain ⟨⟨σ₁, h₁⟩, a₂⟩ := a
  refine ⟨⟨σ₁ - z.re, fun s hs => ?_⟩, fun s hs t ht => ?_⟩
  · show s + z ∈ U
    apply h₁
    simp only [mem_rightOf, Complex.add_re] at hs ⊢
    linarith
  · show s + t + z ∈ U
    have := a₂ _ hs t ht
    rwa [add_right_comm] at this

theorem IsRightDomain.isPreconnected (a : IsRightDomain U) : IsPreconnected U := by
  obtain ⟨⟨σ, hσ⟩, a₂⟩ := a
  have hconv : IsPreconnected (rightOf σ) := (convex_halfSpace_re_gt σ).isPreconnected
  refine isPreconnected_of_forall ((σ + 1 : ℝ) : ℂ) fun y hy => ?_
  have hray : IsPreconnected ((fun t : ℝ => y + t) '' Ici 0) :=
    isPreconnected_Ici.image _ (by fun_prop : Continuous fun t : ℝ => y + (t : ℂ)).continuousOn
  have hT : (0 : ℝ) ≤ |σ - y.re| + 1 := by positivity
  have hmem : y + ((|σ - y.re| + 1 : ℝ) : ℂ) ∈ rightOf σ := by
    simp only [mem_rightOf, Complex.add_re, Complex.ofReal_re]
    have := le_abs_self (σ - y.re)
    linarith
  refine ⟨(fun t : ℝ => y + t) '' Ici 0 ∪ rightOf σ, union_subset ?_ hσ, Or.inr ?_,
    Or.inl ⟨0, mem_Ici.mpr le_rfl, by simp⟩, IsPreconnected.union _ ⟨_, hT, rfl⟩ hmem hray hconv⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact a₂ y hy t ht
  · simp only [mem_rightOf, Complex.ofReal_re]
    linarith

namespace EqRight

@[refl] theorem refl (h : ℂ → ℂ) : EqRight h h := ⟨0, fun _ _ => rfl⟩

theorem symm (a : EqRight H h) : EqRight h H := by
  obtain ⟨σ, e⟩ := a
  exact ⟨σ, e.symm⟩

theorem map₂ (f : ℂ → ℂ → ℂ) (a : EqRight H h) (b : EqRight H' h') :
    EqRight (fun s => f (H s) (H' s)) fun s => f (h s) (h' s) := by
  obtain ⟨σ₁, e₁⟩ := a
  obtain ⟨σ₂, e₂⟩ := b
  refine ⟨max σ₁ σ₂, fun s hs => ?_⟩
  have h1 := e₁ (rightOf_subset (le_max_left _ _) hs)
  have h2 := e₂ (rightOf_subset (le_max_right _ _) hs)
  simp only [h1, h2]

theorem trans (a : EqRight H h) (b : EqRight h h') : EqRight H h' := by
  obtain ⟨σ₁, e₁⟩ := a
  obtain ⟨σ₂, e₂⟩ := b
  exact ⟨max σ₁ σ₂, fun s hs => (e₁ (rightOf_subset (le_max_left _ _) hs)).trans
    (e₂ (rightOf_subset (le_max_right _ _) hs))⟩

end EqRight

theorem eventuallyEq_of_isPreconnected (hU : IsPreconnected U) (hσ : rightOf σ ⊆ U) (a : MeromorphicOn H U)
    (b : MeromorphicOn H' U) (e : EqRight H H') (hs : s ∈ U) : H =ᶠ[𝓝[≠] s] H' := by
  obtain ⟨τ, eτ⟩ := e
  have hxσ : ((max σ τ + 1 : ℝ) : ℂ) ∈ rightOf σ := by
    simp only [mem_rightOf, Complex.ofReal_re]
    linarith [le_max_left σ τ]
  have hxτ : ((max σ τ + 1 : ℝ) : ℂ) ∈ rightOf τ := by
    simp only [mem_rightOf, Complex.ofReal_re]
    linarith [le_max_right σ τ]
  have hd : MeromorphicOn (H - H') U := a.sub b
  have htop : meromorphicOrderAt (H - H') ((max σ τ + 1 : ℝ) : ℂ) = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    apply nhdsWithin_le_nhds
    filter_upwards [(isOpen_rightOf τ).mem_nhds hxτ] with z hz
    simp [eτ hz]
  have hs' : meromorphicOrderAt (H - H') s = ⊤ := by
    by_contra hne
    exact hd.meromorphicOrderAt_ne_top_of_isPreconnected hU hs (hσ hxσ) hne htop
  rw [meromorphicOrderAt_eq_top_iff] at hs'
  filter_upwards [hs'] with z hz
  simpa [sub_eq_zero] using hz

def LaurentCoeff (H : ℂ → ℂ) (s₀ : ℂ) (n : ℤ) (c : ℂ) : Prop := LaurentConst (fun s => (s - s₀) ^ (-n) * H s) s₀ c

theorem laurentConst_congr (a : LaurentConst H s₀ c) (e : H =ᶠ[𝓝[≠] s₀] H') : LaurentConst H' s₀ c := by
  obtain ⟨p, hp, t⟩ := a
  exact ⟨p, hp, t.congr' (e.mono fun s hs => by simp only [hs])⟩

theorem laurentConst_of_tendsto (a : Tendsto H (𝓝[≠] s₀) (𝓝 c)) : LaurentConst H s₀ c := ⟨0, by simp, by simpa using a⟩

theorem laurentConst_add (a : LaurentConst H s₀ c) (b : LaurentConst H' s₀ c') :
    LaurentConst (fun s => H s + H' s) s₀ (c + c') := by
  obtain ⟨p, hp, tp⟩ := a
  obtain ⟨q, hq, tq⟩ := b
  refine ⟨p + q, by simp [hp, hq], (tp.add tq).congr fun s => ?_⟩
  simp only [Polynomial.eval_add]
  ring

theorem laurentConst_const_mul (z : ℂ) (a : LaurentConst H s₀ c) : LaurentConst (fun s => z * H s) s₀ (z * c) := by
  obtain ⟨p, hp, tp⟩ := a
  refine ⟨Polynomial.C z * p, by simp [hp], (tp.const_mul z).congr fun s => ?_⟩
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  ring

theorem laurentConst_unique (a : LaurentConst H s₀ c) (b : LaurentConst H s₀ c') : c = c' := by
  obtain ⟨q, hq, tq⟩ := b
  obtain ⟨p, hp, tp⟩ := a
  refine laurentConst_eq_of_tendsto (fun s => H s - q.eval (s - s₀)⁻¹) s₀ c c'
    ⟨p - q, by simp [hp, hq], tp.congr fun s => ?_⟩ tq
  simp only [Polynomial.eval_sub]
  ring

private theorem laurentConst_add_poly_eval_inv {F : ℂ → ℂ} {s₀ c : ℂ} (a : LaurentConst F s₀ c) (q : Polynomial ℂ)
    (hq : q.coeff 0 = 0) : LaurentConst (fun s => F s + q.eval (s - s₀)⁻¹) s₀ c := by
  obtain ⟨p, hp, tp⟩ := a
  refine ⟨p + q, by simp [hp, hq], tp.congr fun s => ?_⟩
  simp only [Polynomial.eval_add]
  ring

theorem laurentConst_div_pow (k : ℕ) : ∀ {g : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}, HasFPowerSeriesAt g p s₀ →
    LaurentConst (fun s => g s / (s - s₀) ^ k) s₀ (p.coeff k) := by
  induction k with
  | zero =>
    intro g p hp
    apply laurentConst_of_tendsto
    have hp0 : p.coeff 0 = g s₀ := hp.coeff_zero 1
    rw [hp0]
    simp only [pow_zero, div_one]
    exact hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  | succ k ih =>
    intro g p hp
    have h1 := ih hp.has_fpower_series_dslope_fslope
    rw [FormalMultilinearSeries.coeff_fslope] at h1
    have h2 := laurentConst_add_poly_eval_inv h1 (Polynomial.C (g s₀) * Polynomial.X ^ (k + 1))
      (by simp [Polynomial.coeff_X_pow])
    refine laurentConst_congr h2 ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hd : s - s₀ ≠ 0 := sub_ne_zero.mpr hs
    rw [dslope_of_ne _ hs, slope_def_field]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    generalize s - s₀ = d at hd ⊢
    rw [inv_pow, pow_succ]
    field_simp
    ring

theorem laurentCoeff_div_pow {g : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} (hg : HasFPowerSeriesAt g p s₀) (i k : ℕ) :
    LaurentCoeff (fun s => g s / (s - s₀) ^ k) s₀ (i - k) (p.coeff i) := by
  unfold LaurentCoeff
  refine laurentConst_congr (laurentConst_div_pow i hg) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hd : s - s₀ ≠ 0 := sub_ne_zero.mpr hs
  rw [neg_sub, zpow_sub₀ hd, zpow_natCast, zpow_natCast]
  field_simp

theorem exists_laurentConst (a : MeromorphicAt H s₀) : ∃ c, LaurentConst H s₀ c := by
  obtain ⟨n, hn⟩ := a
  obtain ⟨p, hp⟩ := hn
  refine ⟨_, laurentConst_congr (laurentConst_div_pow n hp) ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hd : s - s₀ ≠ 0 := sub_ne_zero.mpr hs
  simp only [smul_eq_mul]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ hd)

theorem exists_laurentCoeff (a : MeromorphicAt H s₀) (n : ℤ) : ∃ c, LaurentCoeff H s₀ n c := by
  have hm : MeromorphicAt (fun s => (s - s₀) ^ (-n) * H s) s₀ :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt.zpow (-n)).mul a
  exact exists_laurentConst hm

@[simp] theorem laurentCoeff_zero : LaurentCoeff H s₀ 0 c ↔ LaurentConst H s₀ c := by
  unfold LaurentCoeff
  simp only [neg_zero, zpow_zero, one_mul]

theorem LaurentCoeff.congr (a : LaurentCoeff H s₀ n c) (e : H =ᶠ[𝓝[≠] s₀] H') : LaurentCoeff H' s₀ n c := laurentConst_congr a (e.mono fun s hs => by simp only [hs])

def IsMerExt (h : ℂ → ℂ) (U : Set ℂ) (H : ℂ → ℂ) : Prop := IsRightDomain U ∧ MeromorphicOn H U ∧ EqRight H h

def IsHolExt (h : ℂ → ℂ) (U : Set ℂ) (H : ℂ → ℂ) : Prop := IsRightDomain U ∧ AnalyticOnNhd ℂ H U ∧ EqRight H h

def IsExtAt (h : ℂ → ℂ) (s₀ : ℂ) (H : ℂ → ℂ) : Prop := ∃ U, s₀ ∈ U ∧ IsMerExt h U H

def Continues (h : ℂ → ℂ) : Prop := ∃ H, IsMerExt h univ H

def contDom (h : ℂ → ℂ) : Set ℂ := {s | ∃ H, IsExtAt h s H}

def CoeffAt (h : ℂ → ℂ) (s₀ : ℂ) (n : ℤ) (c : ℂ) : Prop := ∃ H, IsExtAt h s₀ H ∧ LaurentCoeff H s₀ n c

def ValueAt (h : ℂ → ℂ) (s₀ c : ℂ) : Prop := ∃ H, IsExtAt h s₀ H ∧ LaurentConst H s₀ c

def HolValueAt (h : ℂ → ℂ) (s₀ c : ℂ) : Prop := ∃ H, IsExtAt h s₀ H ∧ AnalyticAt ℂ H s₀ ∧ H s₀ = c

abbrev ResidueAt (h : ℂ → ℂ) (s₀ c : ℂ) : Prop := CoeffAt h s₀ (-1) c

def PoleLE (h : ℂ → ℂ) (s₀ : ℂ) (k : ℕ) : Prop := ∃ H, IsExtAt h s₀ H ∧ ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt H s₀

open Classical in

def laurent (h : ℂ → ℂ) (s₀ : ℂ) (n : ℤ) : ℂ := if e : ∃ c, CoeffAt h s₀ n c then e.choose else 0

def cont (h : ℂ → ℂ) (s : ℂ) : ℂ := laurent h s 0

theorem IsHolExt.isMerExt (a : IsHolExt h U H) : IsMerExt h U H := ⟨a.1, a.2.1.meromorphicOn, a.2.2⟩

theorem IsMerExt.isExtAt (a : IsMerExt h U H) (hs : s₀ ∈ U) : IsExtAt h s₀ H := ⟨U, hs, a⟩

theorem IsMerExt.mono (a : IsMerExt h U H) (b : IsRightDomain U') (e : U' ⊆ U) : IsMerExt h U' H := ⟨b, fun x hx => a.2.1 x (e hx), a.2.2⟩

theorem isMerExt_univ : IsMerExt h univ H ↔ Meromorphic H ∧ EqRight H h := ⟨fun a => ⟨fun x => a.2.1 x (mem_univ x), a.2.2⟩, fun a => ⟨isRightDomain_univ, fun x _ => a.1 x, a.2⟩⟩

theorem IsMerExt.eventuallyEq_of_isPreconnected (a : IsMerExt h U H) (e : U' ⊆ U) (hU : IsPreconnected U') (hσ : rightOf σ ⊆ U')
    (b : MeromorphicOn H' U') (e' : EqRight H' h) (hs : s ∈ U') : H =ᶠ[𝓝[≠] s] H' := GlobalTheory.Cont.eventuallyEq_of_isPreconnected hU hσ (fun x hx => a.2.1 x (e hx)) b (a.2.2.trans e'.symm) hs

namespace IsExtAt

theorem meromorphicAt (a : IsExtAt h s₀ H) : MeromorphicAt H s₀ := by
  obtain ⟨U, hs, hU⟩ := a
  exact hU.2.1 s₀ hs

theorem eqRight (a : IsExtAt h s₀ H) : EqRight H h := by
  obtain ⟨U, hs, hU⟩ := a
  exact hU.2.2

theorem eventuallyEq (a : IsExtAt h s₀ H) (b : IsExtAt h s₀ H') : H =ᶠ[𝓝[≠] s₀] H' := by
  obtain ⟨U, hs, hU, hm, he⟩ := a
  obtain ⟨U', hs', hU', hm', he'⟩ := b
  have hI := hU.inter hU'
  obtain ⟨σ, hσ⟩ := hI.1
  exact eventuallyEq_of_isPreconnected hI.isPreconnected hσ (fun x hx => hm x hx.1) (fun x hx => hm' x hx.2)
    (he.trans he'.symm) ⟨hs, hs'⟩

theorem congr (a : IsExtAt h s₀ H) (e : EqRight h h') : IsExtAt h' s₀ H := by
  obtain ⟨U, hs, hU, hm, he⟩ := a
  exact ⟨U, hs, hU, hm, he.trans e⟩

theorem map₂ (f : ℂ → ℂ → ℂ) (hf : ∀ s, MeromorphicAt H s → MeromorphicAt H' s → MeromorphicAt (fun s => f (H s) (H' s)) s)
    (a : IsExtAt h s₀ H) (b : IsExtAt h' s₀ H') : IsExtAt (fun s => f (h s) (h' s)) s₀ fun s => f (H s) (H' s) := by
  obtain ⟨U, hs, hU, hm, he⟩ := a
  obtain ⟨U', hs', hU', hm', he'⟩ := b
  exact ⟨U ∩ U', ⟨hs, hs'⟩, hU.inter hU', fun x hx => hf x (hm x hx.1) (hm' x hx.2), he.map₂ f he'⟩

theorem add (a : IsExtAt h s₀ H) (b : IsExtAt h' s₀ H') : IsExtAt (fun s => h s + h' s) s₀ fun s => H s + H' s := map₂ (fun x y => x + y) (fun _ h1 h2 => h1.add h2) a b

theorem mul (a : IsExtAt h s₀ H) (b : IsExtAt h' s₀ H') : IsExtAt (fun s => h s * h' s) s₀ fun s => H s * H' s := map₂ (fun x y => x * y) (fun _ h1 h2 => h1.mul h2) a b

theorem div (a : IsExtAt h s₀ H) (b : IsExtAt h' s₀ H') : IsExtAt (fun s => h s / h' s) s₀ fun s => H s / H' s := map₂ (fun x y => x / y) (fun _ h1 h2 => h1.div h2) a b

theorem comp_add {z : ℂ} (a : IsExtAt h (s₀ + z) H) : IsExtAt (fun s => h (s + z)) s₀ fun s => H (s + z) := by
  obtain ⟨U, hs, hU, hm, σ, he⟩ := a
  refine ⟨(· + z) ⁻¹' U, hs, hU.preimage_add z, fun x hx => ?_, σ - z.re, fun x hx => he ?_⟩
  · exact (hm (x + z) hx).comp_analyticAt (g := fun w => w + z) (by fun_prop)
  · simp only [mem_rightOf, Complex.add_re] at hx ⊢
    linarith

theorem update (a : IsExtAt h s₀ H) (c : ℂ) : IsExtAt h s₀ (Function.update H s₀ c) := by
  obtain ⟨U, hs, hU, hm, σ, he⟩ := a
  have hev : ∀ x, Function.update H s₀ c =ᶠ[𝓝[≠] x] H := by
    intro x
    by_cases hx : x = s₀
    · rw [hx]
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact Function.update_of_ne hy _ _
    · filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hx)] with y hy
      exact Function.update_of_ne hy _ _
  refine ⟨U, hs, hU, fun x hx => (hm x hx).congr (hev x).symm, max σ s₀.re, fun x hx => ?_⟩
  have hne : x ≠ s₀ := by
    rintro rfl
    simp [mem_rightOf] at hx
  rw [Function.update_of_ne hne]
  exact he (rightOf_subset (le_max_left _ _) hx)

private theorem isOpen_setOf_meromorphicAt (H : ℂ → ℂ) : IsOpen {x | MeromorphicAt H x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have h1 := (hx : MeromorphicAt H x).eventually_analyticAt
  rw [eventually_nhdsWithin_iff] at h1
  filter_upwards [h1] with y hy
  by_cases hyx : y = x
  · rw [hyx]
    exact hx
  · exact (hy hyx).meromorphicAt

private theorem isOpen_setOf_add_nonneg_real_mem {W : Set ℂ} {σ : ℝ} (hW : IsOpen W) (hσ : rightOf σ ⊆ W) :
    IsOpen {x : ℂ | ∀ t : ℝ, 0 ≤ t → x + t ∈ W} := by
  rw [Metric.isOpen_iff]
  intro x hx
  obtain ⟨T, hT0, hT⟩ : ∃ T : ℝ, 0 ≤ T ∧ σ + 1 < x.re + T :=
    ⟨|σ + 1 - x.re| + 1, by positivity, by linarith [le_abs_self (σ + 1 - x.re)]⟩
  have hK : IsCompact ((fun t : ℝ => x + t) '' Icc 0 T) :=
    isCompact_Icc.image (by fun_prop : Continuous fun t : ℝ => x + (t : ℂ))
  have hKW : (fun t : ℝ => x + t) '' Icc 0 T ⊆ W := by
    rintro _ ⟨t, ht, rfl⟩
    exact hx t ht.1
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_thickening_subset_open hW hKW
  refine ⟨min δ 1, lt_min hδ one_pos, fun y hy t ht => ?_⟩
  rw [Metric.mem_ball] at hy
  rcases le_or_gt t T with htT | htT
  · apply hδW
    rw [Metric.mem_thickening_iff]
    refine ⟨x + t, ⟨t, ⟨ht, htT⟩, rfl⟩, ?_⟩
    rw [dist_add_right]
    exact lt_of_lt_of_le hy (min_le_left _ _)
  · apply hσ
    have h1 : |(y - x).re| ≤ ‖y - x‖ := Complex.abs_re_le_norm _
    rw [← dist_eq_norm, Complex.sub_re] at h1
    have h2 := abs_lt.mp (lt_of_le_of_lt h1 (lt_of_lt_of_le hy (min_le_right _ _)))
    simp only [mem_rightOf, Complex.add_re, Complex.ofReal_re]
    linarith [h2.1]

private theorem exists_isOpen_isMerExt_of_isExtAt (a : IsExtAt h s₀ H) : ∃ U, IsOpen U ∧ s₀ ∈ U ∧ IsMerExt h U H := by
  obtain ⟨U, hs, ⟨⟨σ, hσ⟩, hst⟩, hm, he⟩ := a
  have hUW : ∀ x ∈ U, ∀ t : ℝ, 0 ≤ t → x + t ∈ {x | MeromorphicAt H x} :=
    fun x hx t ht => hm _ (hst x hx t ht)
  have hσW : rightOf σ ⊆ {x | MeromorphicAt H x} := fun x hx => hm x (hσ hx)
  refine ⟨{x : ℂ | ∀ t : ℝ, 0 ≤ t → x + t ∈ {x | MeromorphicAt H x}},
    isOpen_setOf_add_nonneg_real_mem (isOpen_setOf_meromorphicAt H) hσW, hUW s₀ hs,
    ⟨⟨σ, fun x hx => hUW x (hσ hx)⟩, fun x hx t ht t' ht' => ?_⟩, fun x hx => ?_, he⟩
  · have := hx (t + t') (add_nonneg ht ht')
    rwa [Complex.ofReal_add, ← add_assoc] at this
  · simpa using hx 0 le_rfl

theorem eventually (a : IsExtAt h s₀ H) : ∀ᶠ s in 𝓝 s₀, IsExtAt h s H := by
  obtain ⟨U, hU, hs, hm⟩ := exists_isOpen_isMerExt_of_isExtAt a
  filter_upwards [hU.mem_nhds hs] with s hs' using ⟨U, hs', hm⟩

theorem exists_isOpen (a : IsExtAt h s₀ H) : ∃ U, IsOpen U ∧ s₀ ∈ U ∧ IsMerExt h U H := exists_isOpen_isMerExt_of_isExtAt a

end IsExtAt

theorem isMerExt_self (a : IsRightDomain U) (b : MeromorphicOn h U) : IsMerExt h U h := ⟨a, b, EqRight.refl h⟩

theorem isExtAt_const (z s₀ : ℂ) : IsExtAt (fun _ => z) s₀ fun _ => z := ⟨univ, mem_univ _, isRightDomain_univ, fun x _ => MeromorphicAt.const z x, EqRight.refl _⟩

theorem IsExtAt.coeffAt_iff (a : IsExtAt h s₀ H) : CoeffAt h s₀ n c ↔ LaurentCoeff H s₀ n c := by
  constructor
  · rintro ⟨H', b, hc⟩
    exact hc.congr (b.eventuallyEq a)
  · intro hc
    exact ⟨H, a, hc⟩

theorem IsExtAt.valueAt_iff (a : IsExtAt h s₀ H) : ValueAt h s₀ c ↔ LaurentConst H s₀ c := by
  constructor
  · rintro ⟨H', b, hc⟩
    exact laurentConst_congr hc (b.eventuallyEq a)
  · intro hc
    exact ⟨H, a, hc⟩

theorem IsExtAt.holValueAt_iff (a : IsExtAt h s₀ H) : HolValueAt h s₀ c ↔ Tendsto H (𝓝[≠] s₀) (𝓝 c) := by
  constructor
  · rintro ⟨H', b, han, hv⟩
    have t : Tendsto H' (𝓝[≠] s₀) (𝓝 c) := by
      rw [← hv]
      exact han.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact t.congr' (b.eventuallyEq a)
  · intro t
    refine ⟨Function.update H s₀ c, a.update c, ?_, by simp⟩
    exact (a.update c).meromorphicAt.analyticAt (continuousAt_update_same.mpr t)

theorem IsExtAt.poleLE_iff (a : IsExtAt h s₀ H) :
    PoleLE h s₀ k ↔ ∃ c, Tendsto (fun s => (s - s₀) ^ k * H s) (𝓝[≠] s₀) (𝓝 c) := by
  have hH := a.meromorphicAt
  have hP : MeromorphicAt (fun s : ℂ => (s - s₀) ^ k) s₀ := (analyticAt_id.sub analyticAt_const).meromorphicAt.pow k
  have hF : MeromorphicAt (fun s => (s - s₀) ^ k * H s) s₀ := hP.mul hH
  have hPord : meromorphicOrderAt (fun s : ℂ => (s - s₀) ^ k) s₀ = (k : WithTop ℤ) :=
    meromorphicOrderAt_pow_id_sub_const
  have hord : meromorphicOrderAt (fun s => (s - s₀) ^ k * H s) s₀ =
      (k : WithTop ℤ) + meromorphicOrderAt H s₀ := by
    rw [← hPord]
    exact meromorphicOrderAt_mul hP hH
  have key : ∀ o : WithTop ℤ, (0 ≤ (k : WithTop ℤ) + o ↔ ((-k : ℤ) : WithTop ℤ) ≤ o) := by
    intro o
    induction o using WithTop.recTopCoe with
    | top => simp
    | coe m =>
      norm_cast
      omega
  rw [tendsto_nhds_iff_meromorphicOrderAt_nonneg hF, hord, key]
  constructor
  · rintro ⟨H', b, hb⟩
    rwa [meromorphicOrderAt_congr (a.eventuallyEq b)]
  · intro hk
    exact ⟨H, a, hk⟩

theorem IsExtAt.coeffAt_of_tendsto (a : IsExtAt h s₀ H) (e : Tendsto (fun s => (s - s₀) ^ k * H s) (𝓝[≠] s₀) (𝓝 c)) :
    CoeffAt h s₀ (-k) c := ⟨H, a, laurentConst_of_tendsto (by simpa using e)⟩

theorem IsExtAt.tendsto_of_poleLE (a : IsExtAt h s₀ H) (b : PoleLE h s₀ k) (e : CoeffAt h s₀ (-k) c) :
    Tendsto (fun s => (s - s₀) ^ k * H s) (𝓝[≠] s₀) (𝓝 c) := by
  obtain ⟨c', hc'⟩ := a.poleLE_iff.mp b
  have h1 := a.coeffAt_iff.mp e
  have h2 := a.coeffAt_iff.mp (a.coeffAt_of_tendsto hc')
  rw [laurentConst_unique h1 h2]
  exact hc'

@[simp] theorem coeffAt_zero : CoeffAt h s₀ 0 c ↔ ValueAt h s₀ c := by
  simp only [CoeffAt, ValueAt, laurentCoeff_zero]

theorem CoeffAt.unique (a : CoeffAt h s₀ n c) (b : CoeffAt h s₀ n c') : c = c' := by
  obtain ⟨H, ha, hca⟩ := a
  exact laurentConst_unique hca (ha.coeffAt_iff.mp b)

theorem ValueAt.unique (a : ValueAt h s₀ c) (b : ValueAt h s₀ c') : c = c' := by
  obtain ⟨H, ha, hca⟩ := a
  exact laurentConst_unique hca (ha.valueAt_iff.mp b)

theorem HolValueAt.valueAt (a : HolValueAt h s₀ c) : ValueAt h s₀ c := by
  obtain ⟨H, ha, han, hv⟩ := a
  subst hv
  exact ⟨H, ha, laurentConst_of_tendsto (han.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)⟩

theorem HolValueAt.unique (a : HolValueAt h s₀ c) (b : HolValueAt h s₀ c') : c = c' := ValueAt.unique a.valueAt b.valueAt

theorem holValueAt_iff_poleLE : HolValueAt h s₀ c ↔ PoleLE h s₀ 0 ∧ ValueAt h s₀ c := by
  constructor
  · intro a
    refine ⟨?_, a.valueAt⟩
    obtain ⟨H, ha, han, -⟩ := a
    exact ⟨H, ha, by simpa using han.meromorphicOrderAt_nonneg⟩
  · rintro ⟨hp, hv⟩
    obtain ⟨H, ha, hk⟩ := id hp
    obtain ⟨c', hc'⟩ := ha.poleLE_iff.mp hp
    simp only [pow_zero, one_mul] at hc'
    have hcc := laurentConst_eq_of_tendsto H s₀ c c' (ha.valueAt_iff.mp hv) hc'
    subst hcc
    exact ha.holValueAt_iff.mpr hc'

theorem IsHolExt.holValueAt (a : IsHolExt h U H) (hs : s₀ ∈ U) : HolValueAt h s₀ (H s₀) := ⟨H, a.isMerExt.isExtAt hs, a.2.1 s₀ hs, rfl⟩

theorem holValueAt_self (a : AnalyticOnNhd ℂ h (rightOf σ)) (hs : σ < s₀.re) : HolValueAt h s₀ (h s₀) := (show IsHolExt h (rightOf σ) h from ⟨isRightDomain_rightOf σ, a, EqRight.refl h⟩).holValueAt hs

theorem Continues.holValueAt (a : Continues h) (hU : IsPreconnected U) (hσ : rightOf σ ⊆ U) (b : AnalyticOnNhd ℂ H U)
    (e : EqRight H h) (hs : s₀ ∈ U) : HolValueAt h s₀ (H s₀) := by
  obtain ⟨H0, hH0⟩ := a
  have ha := hH0.isExtAt (mem_univ s₀)
  rw [ha.holValueAt_iff]
  have heq : H0 =ᶠ[𝓝[≠] s₀] H := eventuallyEq_of_isPreconnected hU hσ (fun x _ => hH0.2.1 x (mem_univ x))
    b.meromorphicOn (hH0.2.2.trans e.symm) hs
  exact ((b s₀ hs).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm

theorem CoeffAt.congr (a : CoeffAt h s₀ n c) (e : EqRight h h') : CoeffAt h' s₀ n c := by
  obtain ⟨H, ha, hc⟩ := a
  exact ⟨H, ha.congr e, hc⟩

theorem ValueAt.congr (a : ValueAt h s₀ c) (e : EqRight h h') : ValueAt h' s₀ c := by
  obtain ⟨H, ha, hc⟩ := a
  exact ⟨H, ha.congr e, hc⟩

theorem HolValueAt.congr (a : HolValueAt h s₀ c) (e : EqRight h h') : HolValueAt h' s₀ c := by
  obtain ⟨H, ha, han, hv⟩ := a
  exact ⟨H, ha.congr e, han, hv⟩

theorem PoleLE.congr (a : PoleLE h s₀ k) (e : EqRight h h') : PoleLE h' s₀ k := by
  obtain ⟨H, ha, hk⟩ := a
  exact ⟨H, ha.congr e, hk⟩

theorem Continues.congr (a : Continues h) (e : EqRight h h') : Continues h' := by
  obtain ⟨H, hU, hm, he⟩ := a
  exact ⟨H, hU, hm, he.trans e⟩

theorem CoeffAt.add (a : CoeffAt h s₀ n c) (b : CoeffAt h' s₀ n c') : CoeffAt (fun s => h s + h' s) s₀ n (c + c') := by
  obtain ⟨H, ha, hca⟩ := a
  obtain ⟨H', hb, hcb⟩ := b
  refine ⟨fun s => H s + H' s, ha.add hb, ?_⟩
  have := laurentConst_add hca hcb
  unfold LaurentCoeff
  simpa only [mul_add] using this

theorem CoeffAt.const_mul (z : ℂ) (a : CoeffAt h s₀ n c) : CoeffAt (fun s => z * h s) s₀ n (z * c) := by
  obtain ⟨H, ha, hca⟩ := a
  refine ⟨fun s => z * H s, (isExtAt_const z s₀).mul ha, ?_⟩
  have := laurentConst_const_mul z hca
  unfold LaurentCoeff
  simpa only [mul_left_comm] using this

theorem ValueAt.add (a : ValueAt h s₀ c) (b : ValueAt h' s₀ c') : ValueAt (fun s => h s + h' s) s₀ (c + c') := by
  obtain ⟨H, ha, hca⟩ := a
  obtain ⟨H', hb, hcb⟩ := b
  exact ⟨fun s => H s + H' s, ha.add hb, laurentConst_add hca hcb⟩

theorem ValueAt.const_mul (z : ℂ) (a : ValueAt h s₀ c) : ValueAt (fun s => z * h s) s₀ (z * c) := by
  obtain ⟨H, ha, hca⟩ := a
  exact ⟨fun s => z * H s, (isExtAt_const z s₀).mul ha, laurentConst_const_mul z hca⟩

theorem holValueAt_const (z s₀ : ℂ) : HolValueAt (fun _ => z) s₀ z := ⟨fun _ => z, isExtAt_const z s₀, analyticAt_const, rfl⟩

theorem HolValueAt.add (a : HolValueAt h s₀ c) (b : HolValueAt h' s₀ c') : HolValueAt (fun s => h s + h' s) s₀ (c + c') := by
  obtain ⟨H, ha, han, rfl⟩ := a
  obtain ⟨H', hb, hbn, rfl⟩ := b
  exact ⟨fun s => H s + H' s, ha.add hb, han.add hbn, rfl⟩

theorem HolValueAt.mul (a : HolValueAt h s₀ c) (b : HolValueAt h' s₀ c') : HolValueAt (fun s => h s * h' s) s₀ (c * c') := by
  obtain ⟨H, ha, han, rfl⟩ := a
  obtain ⟨H', hb, hbn, rfl⟩ := b
  exact ⟨fun s => H s * H' s, ha.mul hb, han.mul hbn, rfl⟩

theorem HolValueAt.div (a : HolValueAt h s₀ c) (b : HolValueAt h' s₀ c') (h0 : c' ≠ 0) :
    HolValueAt (fun s => h s / h' s) s₀ (c / c') := by
  obtain ⟨H, ha, han, rfl⟩ := a
  obtain ⟨H', hb, hbn, rfl⟩ := b
  exact ⟨fun s => H s / H' s, ha.div hb, han.div hbn h0, rfl⟩

theorem holValueAt_prod {ι : Type*} (T : Finset ι) {f : ι → ℂ → ℂ} {z : ι → ℂ} (a : ∀ i ∈ T, HolValueAt (f i) s₀ (z i)) :
    HolValueAt (fun s => ∏ i ∈ T, f i s) s₀ (∏ i ∈ T, z i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using holValueAt_const 1 s₀
  | @insert j T hj ih =>
    simp only [Finset.prod_insert hj]
    exact (a j (Finset.mem_insert_self j T)).mul (ih fun i hi => a i (Finset.mem_insert_of_mem hi))

theorem HolValueAt.comp_add {z : ℂ} (a : HolValueAt h (s₀ + z) c) : HolValueAt (fun s => h (s + z)) s₀ c := by
  obtain ⟨H, ha, han, hv⟩ := a
  exact ⟨fun s => H (s + z), ha.comp_add, han.comp (f := fun s => s + z) (by fun_prop), hv⟩

theorem PoleLE.mul_hol (a : PoleLE h s₀ k) (e : CoeffAt h s₀ (-k) c) (b : HolValueAt h' s₀ c') :
    PoleLE (fun s => h s * h' s) s₀ k ∧ CoeffAt (fun s => h s * h' s) s₀ (-k) (c * c') := by
  obtain ⟨H, ha, hk⟩ := id a
  obtain ⟨H', hb, hbn, rfl⟩ := b
  have t1 := ha.tendsto_of_poleLE a e
  have t2 : Tendsto H' (𝓝[≠] s₀) (𝓝 (H' s₀)) := hbn.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hm := ha.mul hb
  have t3 : Tendsto (fun s => (s - s₀) ^ k * (H s * H' s)) (𝓝[≠] s₀) (𝓝 (c * H' s₀)) :=
    (t1.mul t2).congr fun s => by ring
  exact ⟨hm.poleLE_iff.mpr ⟨_, t3⟩, hm.coeffAt_of_tendsto t3⟩

theorem isOpen_contDom (h : ℂ → ℂ) : IsOpen (contDom h) := by
  rw [isOpen_iff_mem_nhds]
  rintro s ⟨H, hs⟩
  exact hs.eventually.mono fun s' hs' => ⟨H, hs'⟩

theorem IsMerExt.subset_contDom (a : IsMerExt h U H) : U ⊆ contDom h := fun _ hs => ⟨H, a.isExtAt hs⟩

theorem isRightDomain_contDom (hs : s₀ ∈ contDom h) : IsRightDomain (contDom h) := by
  obtain ⟨H, U, hsU, hU, hm, he⟩ := hs
  obtain ⟨σ, hσ⟩ := hU.1
  refine ⟨⟨σ, hσ.trans (IsMerExt.subset_contDom ⟨hU, hm, he⟩)⟩, fun s hs t ht => ?_⟩
  obtain ⟨H', U', hsU', hU', hm', he'⟩ := hs
  exact ⟨H', U', hU'.2 s hsU' t ht, hU', hm', he'⟩

theorem CoeffAt.laurent_eq (a : CoeffAt h s₀ n c) : laurent h s₀ n = c := by
  have hex : ∃ c, CoeffAt h s₀ n c := ⟨c, a⟩
  unfold laurent
  rw [dif_pos hex]
  exact CoeffAt.unique hex.choose_spec a

theorem coeffAt_laurent (hs : s₀ ∈ contDom h) (n : ℤ) : CoeffAt h s₀ n (laurent h s₀ n) := by
  obtain ⟨H, ha⟩ := hs
  obtain ⟨c, hc⟩ := exists_laurentCoeff ha.meromorphicAt n
  have hC : CoeffAt h s₀ n c := ⟨H, ha, hc⟩
  rw [hC.laurent_eq]
  exact hC

theorem coeffAt_iff : CoeffAt h s₀ n c ↔ s₀ ∈ contDom h ∧ laurent h s₀ n = c := by
  constructor
  · intro a
    obtain ⟨H, ha, -⟩ := id a
    exact ⟨⟨H, ha⟩, a.laurent_eq⟩
  · rintro ⟨hs, rfl⟩
    exact coeffAt_laurent hs n

theorem valueAt_iff : ValueAt h s₀ c ↔ s₀ ∈ contDom h ∧ cont h s₀ = c := by
  rw [← coeffAt_zero, coeffAt_iff]
  exact Iff.rfl

theorem ValueAt.cont_eq (a : ValueAt h s₀ c) : cont h s₀ = c := (valueAt_iff.mp a).2

theorem IsExtAt.cont_eventuallyEq (a : IsExtAt h s₀ H) : cont h =ᶠ[𝓝[≠] s₀] H := by
  have h1 := a.meromorphicAt.eventually_analyticAt
  have h2 : ∀ᶠ s in 𝓝[≠] s₀, IsExtAt h s H := nhdsWithin_le_nhds a.eventually
  filter_upwards [h1, h2] with s hs1 hs2
  exact (HolValueAt.valueAt ⟨H, hs2, hs1, rfl⟩).cont_eq

theorem meromorphicOn_cont (h : ℂ → ℂ) : MeromorphicOn (cont h) (contDom h) := by
  intro s hs
  obtain ⟨H, ha⟩ := hs
  exact ha.meromorphicAt.congr ha.cont_eventuallyEq.symm

theorem HolValueAt.analyticAt_cont (a : HolValueAt h s₀ c) : AnalyticAt ℂ (cont h) s₀ := by
  obtain ⟨H, ha, han, hv⟩ := id a
  have e1 := ha.cont_eventuallyEq
  have e2 : cont h s₀ = H s₀ := by rw [a.valueAt.cont_eq, hv]
  have e3 : H =ᶠ[𝓝 s₀] cont h := by
    have e4 := e1.symm
    rw [EventuallyEq, eventually_nhdsWithin_iff] at e4
    filter_upwards [e4] with s hs
    by_cases hss : s = s₀
    · rw [hss]
      exact e2.symm
    · exact hs hss
  exact han.congr e3

theorem eqOn_cont (a : AnalyticOnNhd ℂ h (rightOf σ)) : EqOn (cont h) h (rightOf σ) := fun _ hs => (holValueAt_self a hs).valueAt.cont_eq

theorem isMerExt_cont (a : AnalyticOnNhd ℂ h (rightOf σ)) : IsMerExt h (contDom h) (cont h) := by
  have hsub : rightOf σ ⊆ contDom h :=
    (isMerExt_self (isRightDomain_rightOf σ) a.meromorphicOn).subset_contDom
  have hmem : ((σ + 1 : ℝ) : ℂ) ∈ rightOf σ := by
    simp only [mem_rightOf, Complex.ofReal_re]
    linarith
  exact ⟨isRightDomain_contDom (hsub hmem), meromorphicOn_cont h, ⟨σ, eqOn_cont a⟩⟩

theorem continues_iff (a : AnalyticOnNhd ℂ h (rightOf σ)) : Continues h ↔ contDom h = univ := by
  constructor
  · rintro ⟨H, hH⟩
    exact eq_univ_of_univ_subset hH.subset_contDom
  · intro e
    refine ⟨cont h, ?_⟩
    rw [← e]
    exact isMerExt_cont a

theorem isMerExt_riemannZeta : IsMerExt (fun s => ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s) univ riemannZeta := by
  refine ⟨isRightDomain_univ, fun s _ => ?_, ⟨1, fun s hs => zeta_eq_tsum_one_div_nat_add_one_cpow hs⟩⟩
  rcases eq_or_ne s 1 with rfl | hs
  · have hGa : AnalyticAt ℂ (Function.update (fun s => (s - 1) * riemannZeta s) 1 1) 1 := by
      refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with z hz
        refine DifferentiableAt.congr_of_eventuallyEq
          ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hz)) ?_
        filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
        exact Function.update_of_ne hw _ _
      · exact continuousAt_update_same.mpr riemannZeta_residue_one
    have hm : MeromorphicAt (fun s => Function.update (fun s => (s - 1) * riemannZeta s) 1 1 s * (s - 1)⁻¹) 1 :=
      hGa.meromorphicAt.mul (analyticAt_id.sub analyticAt_const).meromorphicAt.inv
    refine hm.congr ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hd : z - 1 ≠ 0 := sub_ne_zero.mpr hz
    rw [Function.update_of_ne hz]
    field_simp
  · have hd : DifferentiableOn ℂ riemannZeta {1}ᶜ := fun x hx => (differentiableAt_riemannZeta hx).differentiableWithinAt
    exact (hd.analyticAt (isOpen_compl_singleton.mem_nhds hs)).meromorphicAt

example : HolValueAt (fun s => ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s) 0 (-1 / 2) ∧
    PoleLE (fun s => ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s) 1 1 ∧ ResidueAt (fun s => ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s) 1 1 ∧
    ValueAt (fun s => ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s) 1 Real.eulerMascheroniConstant := by
  have h1 : Tendsto (fun s => (s - 1) ^ 1 * riemannZeta s) (𝓝[≠] 1) (𝓝 1) := by simpa using riemannZeta_residue_one
  have a := fun s => isMerExt_riemannZeta.isExtAt (mem_univ s)
  refine ⟨(a 0).holValueAt_iff.2 ?_, (a 1).poleLE_iff.2 ⟨1, h1⟩, (a 1).coeffAt_of_tendsto h1,
    _, a 1, Polynomial.X, by simp, by simpa using tendsto_riemannZeta_sub_one_div⟩
  exact riemannZeta_zero ▸ (differentiableAt_riemannZeta zero_ne_one).continuousAt.tendsto.mono_left nhdsWithin_le_nhds

example : ValueAt (fun s => s⁻¹) 0 0 ∧ ∀ c, ¬ HolValueAt (fun s => s⁻¹) 0 c := by
  have a : IsExtAt (fun s : ℂ => s⁻¹) 0 fun s => s⁻¹ :=
    (isMerExt_self isRightDomain_univ fun s _ => (MeromorphicAt.id s).inv).isExtAt trivial
  exact ⟨⟨_, a, Polynomial.X, by simp, by simp⟩, fun c e => not_tendsto_atTop_of_tendsto_nhds (a.holValueAt_iff.1 e).norm
    (tendsto_norm_cobounded_atTop.comp tendsto_inv₀_nhdsNE_zero)⟩

end GlobalTheory.Cont

end
