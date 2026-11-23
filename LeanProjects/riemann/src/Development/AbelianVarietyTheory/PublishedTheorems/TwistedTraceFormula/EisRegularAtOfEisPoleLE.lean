import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight

noncomputable section

open scoped NNReal ComplexConjugate
open Filter Topology Set Metric MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.Mem.Th (InfF CptF)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Eis

variable {D : D7} (V : HSp D)

def EisRegularAt (Φ : ℂ → GA D (dblSp V) → ℂ) (s₀ : ℂ) (k : ℕ) : Prop :=
  ∃ (r : ℝ) (H : ℂ → GA D (dblSp V) → ℂ), 0 < r ∧
    (∀ s ∈ ball s₀ r, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * eisCont V Φ s g) ∧
    (∀ g, DifferentiableOn ℂ (H · g) (ball s₀ r)) ∧
    ContinuousOn (fun x : ℂ × GA D (dblSp V) => H x.1 x.2) (ball s₀ r ×ˢ univ) ∧
    ∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball s₀ r, ∀ g, ‖H s g‖ ≤ C * Grow.height (dblSp V) g ^ N

def petCoef (m : Measure (GA D V)) (f₁ f₂ : GA D V → ℂ) : GA D V → ℂ := fun g => Cusp.petersson V m (rTr V g f₁) f₂

def BasicIdentity (μ : (AE D)ˣ →* Circle) (m : Measure (GA D V)) (Φ : GA D (dblSp V) → ℂ) (f₁ f₂ : GA D V → ℂ) : Prop :=
  DblConv V μ m (eis V Φ) f₁ f₂ ∧ ZetaConvH D.sp.cm.sig (gram_hdbl V) m Φ (petCoef V m f₁ f₂) ∧
    dblInt V μ m (eis V Φ) f₁ f₂ = zetaH D.sp.cm.sig (gram_hdbl V) m Φ (petCoef V m f₁ f₂)

end GlobalTheory.Eis

namespace GlobalTheory.Published

open GlobalTheory.Eis

def DoublingMethod : Prop :=
  ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a →
    HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) →
    ∀ (μ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D μ → ResEta D μ b →
    ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ →
      (EisContinues V (flat V a φ s₁) ∧ ∀ s₀, ∃ k, EisRegularAt V (flat V a φ s₁) s₀ k) ∧
      (V.rank < b → EisPoleLE V (flat V a φ s₁) (((b : ℂ) - V.rank) / 2) 1) ∧
      ∀ θ : InfF D, IsInfFam θ → V.SigOK → ∀ A : CptF V, Cusp.IsCartanFrame V A →
        ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ ∈ Cusp.A0 θ V A, ∀ f₂ ∈ Cusp.A0 θ V A,
          (∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → BasicIdentity V μ m (flat V a φ s₁ s) f₁ f₂) ∧
          ZetaContinues V μ m (flat V a φ s₁) f₁ f₂

end GlobalTheory.Published

namespace GlobalTheory.Eis

theorem dslope_family {X : Type} [TopologicalSpace X] {H : ℂ → X → ℂ} {w : X → ℝ} {s₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : ∀ x, DifferentiableOn ℂ (H · x) (ball s₀ r))
    (hc : ContinuousOn (fun p : ℂ × X => H p.1 p.2) (ball s₀ r ×ˢ univ))
    (hb : ∀ s ∈ ball s₀ r, ∀ x, ‖H s x‖ ≤ w x) (h0 : ∀ x, H s₀ x = 0) :
    (∀ x, DifferentiableOn ℂ (dslope (H · x) s₀) (ball s₀ (r / 2))) ∧
    ContinuousOn (fun p : ℂ × X => dslope (H · p.2) s₀ p.1) (ball s₀ (r / 2) ×ˢ univ) ∧
    ∀ s ∈ ball s₀ (r / 2), ∀ x, ‖dslope (H · x) s₀ s‖ ≤ w x / r := by
  have hsub : ball s₀ (r / 2) ⊆ ball s₀ r := ball_subset_ball (by linarith)
  have hsub' : closedBall s₀ (r / 2) ⊆ ball s₀ r := closedBall_subset_ball (by linarith)
  have h1 : ∀ x, DifferentiableOn ℂ (dslope (H · x) s₀) (ball s₀ r) := fun x =>
    (Complex.differentiableOn_dslope (ball_mem_nhds _ hr)).2 (hd x)
  refine ⟨fun x => (h1 x).mono hsub, ?_, fun s hs x => Complex.norm_dslope_le_div_of_mapsTo_ball (hd x)
    (fun z hz => by simpa [h0] using hb z hz x) (hsub hs)⟩
  rintro ⟨s₁, x₀⟩ ⟨hs₁, -⟩
  have h2 : ContinuousWithinAt (fun p : ℂ × X => dslope (H · x₀) s₀ p.1) (ball s₀ (r / 2) ×ˢ univ) (s₁, x₀) :=
    (((h1 x₀).continuousOn.continuousAt (isOpen_ball.mem_nhds (hsub hs₁))).comp_of_eq continuousAt_fst rfl).continuousWithinAt
  have h3 : Tendsto (fun p : ℂ × X => dslope (H · p.2) s₀ p.1 - dslope (H · x₀) s₀ p.1)
      (𝓝[ball s₀ (r / 2) ×ˢ univ] (s₁, x₀)) (𝓝 0) := by
    refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε => ?_
    have h4 : ∀ᶠ x in 𝓝 x₀, ∀ z ∈ closedBall s₀ (r / 2), ‖H z x - H z x₀‖ < ε * (r / 4) := by
      refine (isCompact_closedBall s₀ (r / 2)).eventually_forall_of_forall_eventually fun z hz => ?_
      have h5 : ∀ y, ContinuousAt (fun p : ℂ × X => H p.1 p.2) (z, y) := fun y =>
        hc.continuousAt ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨hsub' hz, trivial⟩)
      have h6 : ContinuousAt (fun p : X × ℂ => ‖H p.2 p.1 - H p.2 x₀‖) (x₀, z) :=
        (((h5 x₀).comp_of_eq (f := fun p : X × ℂ => (p.2, p.1)) (by fun_prop) rfl).sub
          ((h5 x₀).comp_of_eq (f := fun p : X × ℂ => (p.2, x₀)) (by fun_prop) rfl)).norm
      exact h6.eventually (gt_mem_nhds (by simpa using by positivity))
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (continuousAt_snd.eventually h4)] with p hp h4
    have h7 := Complex.norm_dslope_le_div_of_mapsTo_ball (f := fun z => H z p.2 - H z x₀) (R₂ := ε * (r / 4))
      (((hd _).sub (hd _)).mono hsub) (fun z hz => by simpa [h0] using (h4 z (ball_subset_closedBall hz)).le) hp.1
    have h8 : dslope (fun z => H z p.2 - H z x₀) s₀ p.1 = dslope (H · p.2) s₀ p.1 - dslope (H · x₀) s₀ p.1 := by
      rcases eq_or_ne p.1 s₀ with e | e
      · rw [e, dslope_same, dslope_same, dslope_same]
        exact deriv_fun_sub ((hd _).differentiableAt (ball_mem_nhds _ hr)) ((hd _).differentiableAt (ball_mem_nhds _ hr))
      · simp only [dslope_of_ne _ e, slope_def_field]; ring
    rw [← h8]
    refine h7.trans_lt ?_
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos hε hr]
  simpa [ContinuousWithinAt] using h3.add h2

variable {D : D7} {V : HSp D} {Φ : ℂ → GA D (dblSp V) → ℂ} {s₀ : ℂ} {j k : ℕ}

theorem EisRegularAt.succ (h : EisRegularAt V Φ s₀ k) : EisRegularAt V Φ s₀ (k + 1) := by
  obtain ⟨r, H, hr, e, hd, hc, C, N, hb⟩ := h
  refine ⟨r, fun s g => (s - s₀) * H s g, hr, fun s hs h0 g => by simp only [e s hs h0]; ring,
    fun g => (differentiableOn_id.sub_const _).mul (hd g), (by fun_prop : ContinuousOn (fun x : ℂ × _ => x.1 - s₀) _).mul hc,
    r * C, N, fun s hs g => ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul (mem_ball_iff_norm.1 hs).le (hb s hs g) (norm_nonneg _) hr.le

theorem EisRegularAt.pred (h : EisRegularAt V Φ s₀ (k + 1)) (hp : EisPoleLE V Φ s₀ j) (hj : j ≤ k) :
    EisRegularAt V Φ s₀ k := by
  obtain ⟨r, H, hr, e, hd, hc, C, N, hb⟩ := h
  have h0 : ∀ g, H s₀ g = 0 := fun g => by
    obtain ⟨E, hE, -⟩ := id (hp.2 g)
    obtain ⟨c, hc⟩ := hE.poleLE_iff.1 (hp.2 g)
    have h1 : Tendsto (fun s => (s - s₀) ^ (k + 1 - j)) (𝓝[≠] s₀) (𝓝 0) :=
      (Continuous.tendsto' (by fun_prop) s₀ 0 (by simp; omega)).mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique (((hd g).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {s₀}ᶜ))) ((zero_mul c ▸ h1.mul hc).congr' ?_)
    filter_upwards [hE.cont_eventuallyEq, self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₀ hr)]
      with s h2 h3 h4
    rw [e s h4 h3, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega), ← h2]
    rfl
  obtain ⟨h1, h2, h3⟩ := dslope_family hr hd hc hb h0
  refine ⟨r / 2, fun s g => dslope (H · g) s₀ s, half_pos hr, fun s hs hs' g => ?_, h1, h2, C / r, N, fun s hs g => ?_⟩
  · have := sub_ne_zero.2 hs'
    simp only [dslope_of_ne _ hs', slope_def_field, h0, e s (ball_subset_ball (by linarith) hs) hs']
    field_simp
    ring
  · rw [div_mul_eq_mul_div]; exact h3 s hs g

theorem EisRegularAt.of_poleLE (h : EisRegularAt V Φ s₀ k) (hp : EisPoleLE V Φ s₀ j) : EisRegularAt V Φ s₀ j := by
  rcases le_total k j with hk | hk
  · exact Nat.le_induction h (fun _ _ => EisRegularAt.succ) j hk
  · exact Nat.decreasingInduction (motive := fun i _ => j ≤ i → EisRegularAt V Φ s₀ i)
      (fun i _ ih hi => (ih (by omega)).pred hp hi) (fun _ => h) hk le_rfl

theorem EisRegularAt.of_eisValueAt {ψ : GA D (dblSp V) → ℂ} (h : EisRegularAt V Φ s₀ k) (hv : EisValueAt V Φ s₀ ψ) :
    ∃ r : ℝ, 0 < r ∧ (∀ g, DifferentiableOn ℂ (eisCont V Φ · g) (ball s₀ r)) ∧
      ContinuousOn (fun x : ℂ × GA D (dblSp V) => eisCont V Φ x.1 x.2) (ball s₀ r ×ˢ univ) ∧
      ∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball s₀ r, ∀ g, ‖eisCont V Φ s g‖ ≤ C * Grow.height (dblSp V) g ^ N := by
  obtain ⟨r, H, hr, e, hd, hc, C, N, hb⟩ := h.of_poleLE (eisValueAt_iff_eisPoleLE.1 hv).1
  have e' : ∀ s ∈ ball s₀ r, ∀ g, eisCont V Φ s g = H s g := fun s hs g => by
    rcases eq_or_ne s s₀ with rfl | h0
    · refine tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] s)
        ((hv.2 g).analyticAt_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (((hd g).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s hr)] with z h1 h2
      rw [e z h2 h1, pow_zero, one_mul]; rfl
    · rw [e s hs h0, pow_zero, one_mul]
  exact ⟨r, hr, fun g => (hd g).congr fun s hs => e' s hs g, hc.congr fun x hx => e' _ hx.1 _, C, N,
    fun s hs g => e' s hs g ▸ hb s hs g⟩

theorem EisRegularAt.eisPoleLE (h : EisRegularAt V Φ s₀ k) (hE : EisContinues V Φ) : EisPoleLE V Φ s₀ k := by
  obtain ⟨r, H, hr, e, hd, -⟩ := h
  refine ⟨hE.1, fun g => ?_⟩
  obtain ⟨E, hE⟩ := hE.2 g
  refine (hE.isExtAt trivial).poleLE_iff.2 ⟨H s₀ g, (((hd g).continuousOn.continuousAt
    (ball_mem_nhds _ hr)).tendsto.mono_left nhdsWithin_le_nhds).congr' ?_⟩
  filter_upwards [(hE.isExtAt (s₀ := s₀) trivial).cont_eventuallyEq, self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₀ hr)] with s h2 h3 h4
  rw [e s h4 h3, ← h2]; rfl

section Consequences

variable (hP : Published.DoublingMethod) (h0 : 0 < V.rank) {a : GL (Fin V.rank) (AE D)} (ha : IsMaj V a)
  (hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a)) {μ : (AE D)ˣ →* Circle} {b : ℕ} (hμ : IsHeckeChar D μ)
  (hb : ResEta D μ b) {s₁ : ℂ} {φ : GA D (dblSp V) → ℂ} (hφ : φ ∈ degPS V a μ s₁)
include hP h0 ha hI hμ hb hφ

theorem basicIdentity_of_mem (hs : (V.rank : ℝ) / 2 < s₁.re) {θ : InfF D} (hθ : IsInfFam θ) (hV : V.SigOK) {A : CptF V}
    (hA : Cusp.IsCartanFrame V A) (m : Measure (GA D V)) [hm : m.IsHaarMeasure] {f₁ f₂ : GA D V → ℂ}
    (h₁ : f₁ ∈ Cusp.A0 θ V A) (h₂ : f₂ ∈ Cusp.A0 θ V A) : BasicIdentity V μ m φ f₁ f₂ := by
  simpa only [flatH_self] using ((hP D V h0 a ha hI μ b hμ hb s₁ φ hφ).2.2 θ hθ hV A hA m hm f₁ h₁ f₂ h₂).1 s₁ hs

end Consequences

end GlobalTheory.Eis

end
