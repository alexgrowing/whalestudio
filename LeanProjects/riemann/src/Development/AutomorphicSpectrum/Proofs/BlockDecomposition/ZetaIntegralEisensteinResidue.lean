import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoeffAtNegOneZetaOfEisCoeffAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelEisensteinContinuationAndPoles
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

open Filter Topology Set Metric GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.Eis

variable {D : D7} {V : HSp D}

theorem laurentCoeff_base {F : ℂ → ℂ} {s₀ : ℂ} (h : ContinuousAt F s₀) :
    LaurentCoeff (fun s => F s / (s - s₀) ^ (0 + 1)) s₀ (-1) (F s₀) := by
  refine laurentConst_of_tendsto ((h.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with s hs
  have : s - s₀ ≠ 0 := sub_ne_zero.2 hs
  simp only [neg_neg, zpow_one, zero_add, pow_one]
  field_simp

theorem laurentCoeff_step {F G : ℂ → ℂ} {s₀ c e : ℂ} {k : ℕ} (hF : ∀ᶠ s in 𝓝[≠] s₀, F s = c + (s - s₀) * G s)
    (hG : LaurentCoeff (fun s => G s / (s - s₀) ^ (k + 1)) s₀ (-1) e) :
    LaurentCoeff (fun s => F s / (s - s₀) ^ (k + 1 + 1)) s₀ (-1) e := by
  have h1 : GlobalTheory.ThetaInner.LaurentConst (fun s => c * (s - s₀)⁻¹ ^ (k + 1)) s₀ 0 :=
    ⟨Polynomial.monomial (k + 1) c, by simp [Polynomial.coeff_monomial], by simp [Polynomial.eval_monomial]⟩
  have h2 := laurentConst_add h1 hG
  rw [zero_add] at h2
  refine laurentConst_congr h2 ?_
  filter_upwards [hF, self_mem_nhdsWithin] with s h3 hs
  have : s - s₀ ≠ 0 := sub_ne_zero.2 hs
  simp only [neg_neg, zpow_one, h3, inv_pow]
  field_simp
  ring

theorem dblInt_family {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ) {m : Measure (GA D V)} (hm : m.IsHaarMeasure)
    {f₁ f₂ : GA D V → ℂ} (h₁ : GlobalTheory.Grow.RapidDec V f₁) (h₂ : GlobalTheory.Grow.RapidDec V f₂)
    {H : ℂ → GA D (dblSp V) → ℂ} {z : ℂ} {r : ℝ}
    (hinv : ∀ s ∈ ball z r, LeftInv (GQ (dblSp V)) (H s))
    (hd : ∀ g, DifferentiableOn ℂ (H · g) (ball z r))
    (hc : ContinuousOn (fun x : ℂ × GA D (dblSp V) => H x.1 x.2) (ball z r ×ˢ univ))
    (hB : ∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball z r, ∀ g, ‖H s g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) :
    (∀ s ∈ ball z r, DblConv V μ m (H s) f₁ f₂) ∧
      DifferentiableOn ℂ (fun s => dblInt V μ m (H s) f₁ f₂) (ball z r) := by
  obtain ⟨C, N, hb⟩ := hB
  obtain ⟨C', c, hio⟩ := GlobalTheory.T.exists_height_doublingEmbedding_le_pow_mul_heights D V
  obtain ⟨bound, hbi, hbd⟩ := GlobalTheory.T.exists_integrable_bound_doubling_integrand_quotient D V μ m hm f₁ f₂ h₁ h₂ C' c hio C N
  have hcont : ∀ s ∈ ball z r, Continuous (H s) := fun s hs =>
    hc.comp_continuous (f := fun g => (s, g)) (by fun_prop) fun g => ⟨hs, trivial⟩
  have hli : ∀ s ∈ ball z r, LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ (H s) f₁ f₂) := fun s hs =>
    leftInv_dblIntegrand hμ (hinv s hs) h₁.1 h₂.1
  have hmeas : ∀ s ∈ ball z r, AEStronglyMeasurable (dblIntegrandQ V μ (H s) f₁ f₂)
      ((autMeasure V m).prod (autMeasure V m)) := by
    intro s hs
    have e' : dblIntegrandQ V μ (H s) f₁ f₂ =
        dblIntegrand V μ (H s) f₁ f₂ ∘ Prod.map (sec (GQ V)) (sec (GQ V)) :=
      funext fun q => (congrArg _ (Prod.ext (mk_sec q.1) (mk_sec q.2)).symm).trans (dblIntegrandQ_mk (hli s hs) _ _)
    rw [e']
    exact ((continuous_dblIntegrand hμ (hcont s hs) h₁.continuous h₂.continuous).measurable.comp
      (measurableEmbedding_sec.measurable.prodMap measurableEmbedding_sec.measurable)).aestronglyMeasurable
  refine ⟨fun s hs => ⟨hli s hs, hbi.mono' (hmeas s hs) (ae_of_all _ fun q => hbd (H s) (hinv s hs) (hb s hs) q)⟩, ?_⟩
  have := GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated
    (μ := (autMeasure V m).prod (autMeasure V m)) (F := fun q s => dblIntegrandQ V μ (H s) f₁ f₂ q)
    (isOpen_ball (x := z) (ε := r)) hmeas
    (ae_of_all _ fun q => by
      simp only [dblIntegrandQ, dblIntegrand]
      exact (((hd _).mul_const _).mul_const _).mul_const _)
    fun x hx => ⟨ball z r, isOpen_ball.mem_nhds hx, bound, hbi,
      ae_of_all _ fun q y hy => hbd (H y) (hinv y hy) (hb y hy) q⟩
  exact this.1

theorem exists_div_family {H : ℂ → GA D (dblSp V) → ℂ} {s₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hinv : ∀ s ∈ ball s₀ r, LeftInv (GQ (dblSp V)) (H s))
    (hd : ∀ g, DifferentiableOn ℂ (H · g) (ball s₀ r))
    (hc : ContinuousOn (fun x : ℂ × GA D (dblSp V) => H x.1 x.2) (ball s₀ r ×ˢ univ))
    (hB : ∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball s₀ r, ∀ g, ‖H s g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) :
    ∃ H' : ℂ → GA D (dblSp V) → ℂ,
      (∀ s ∈ ball s₀ (r / 2), LeftInv (GQ (dblSp V)) (H' s)) ∧
      (∀ g, DifferentiableOn ℂ (H' · g) (ball s₀ (r / 2))) ∧
      ContinuousOn (fun x : ℂ × GA D (dblSp V) => H' x.1 x.2) (ball s₀ (r / 2) ×ˢ univ) ∧
      (∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball s₀ (r / 2), ∀ g, ‖H' s g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) ∧
      ∀ s g, H s g = H s₀ g + (s - s₀) * H' s g := by
  obtain ⟨C, N, hb⟩ := hB
  have hs₀ : s₀ ∈ ball s₀ r := mem_ball_self hr
  have hKd : ∀ g, DifferentiableOn ℂ (fun s => H s g - H s₀ g) (ball s₀ r) := fun g => (hd g).sub_const _
  have hKc : ContinuousOn (fun p : ℂ × GA D (dblSp V) => H p.1 p.2 - H s₀ p.2) (ball s₀ r ×ˢ univ) :=
    hc.sub (hc.comp (f := fun p : ℂ × GA D (dblSp V) => (s₀, p.2)) (by fun_prop) fun p _ => ⟨hs₀, trivial⟩)
  have hKb : ∀ s ∈ ball s₀ r, ∀ g, ‖H s g - H s₀ g‖ ≤ 2 * C * GlobalTheory.Grow.height (dblSp V) g ^ N := fun s hs g => by
    have := norm_sub_le (H s g) (H s₀ g)
    linarith [hb s hs g, hb s₀ hs₀ g]
  obtain ⟨h1, h2, h3⟩ := dslope_family (H := fun s g => H s g - H s₀ g)
    (w := fun g => 2 * C * GlobalTheory.Grow.height (dblSp V) g ^ N) hr hKd hKc hKb (fun g => sub_self _)
  refine ⟨fun s g => dslope (fun z => H z g - H s₀ g) s₀ s, fun s hs γ hγ g => ?_, h1, h2,
    ⟨2 * C / r, N, fun s hs g => ?_⟩, fun s g => ?_⟩
  · have hK : ∀ z ∈ ball s₀ r, H z (γ * g) - H s₀ (γ * g) = H z g - H s₀ g := fun z hz => by
      rw [hinv z hz γ hγ g, hinv s₀ hs₀ γ hγ g]
    rcases eq_or_ne s s₀ with rfl | h0
    · simp only [dslope_same]
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [ball_mem_nhds s hr] with z hz using hK z hz
    · simp only [dslope_of_ne _ h0, slope_def_field, hK s (ball_subset_ball (by linarith) hs), sub_self]
  · have := h3 s hs g
    rwa [mul_div_right_comm] at this
  · rcases eq_or_ne s s₀ with rfl | h0
    · simp
    · have := sub_ne_zero.2 h0
      simp only [dslope_of_ne _ h0, slope_def_field, sub_self, sub_zero]
      field_simp
      ring

theorem dblConv_smul {μ : (AE D)ˣ →* Circle} {m : Measure (GA D V)} {E : GA D (dblSp V) → ℂ} {f₁ f₂ : GA D V → ℂ}
    (h : DblConv V μ m E f₁ f₂) (c : ℂ) : DblConv V μ m (c • E) f₁ f₂ := by
  obtain ⟨hl, hi⟩ := h
  have e2 : dblIntegrand V μ (c • E) f₁ f₂ = fun q => c * dblIntegrand V μ E f₁ f₂ q :=
    funext fun q => by simp only [dblIntegrand, Pi.smul_apply, smul_eq_mul]; ring
  have e3 : dblIntegrandQ V μ (c • E) f₁ f₂ = fun q => c * dblIntegrandQ V μ E f₁ f₂ q :=
    funext fun q => by simp only [dblIntegrandQ, e2]
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · rw [e2]; exact congrArg _ (hl γ hγ g)
  · rw [e3]; exact hi.const_mul _

theorem exists_coeff_family {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ) {m : Measure (GA D V)} (hm : m.IsHaarMeasure)
    {f₁ f₂ : GA D V → ℂ} (h₁ : GlobalTheory.Grow.RapidDec V f₁) (h₂ : GlobalTheory.Grow.RapidDec V f₂) (s₀ : ℂ) (k : ℕ) :
    ∀ (H : ℂ → GA D (dblSp V) → ℂ) (r : ℝ), 0 < r →
      (∀ s ∈ ball s₀ r, LeftInv (GQ (dblSp V)) (H s)) →
      (∀ g, DifferentiableOn ℂ (H · g) (ball s₀ r)) →
      ContinuousOn (fun x : ℂ × GA D (dblSp V) => H x.1 x.2) (ball s₀ r ×ˢ univ) →
      (∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball s₀ r, ∀ g, ‖H s g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) →
      ∃ E : GA D (dblSp V) → ℂ, (∀ g, LaurentCoeff (fun s => H s g / (s - s₀) ^ (k + 1)) s₀ (-1) (E g)) ∧
        LaurentCoeff (fun s => dblInt V μ m (H s) f₁ f₂ / (s - s₀) ^ (k + 1)) s₀ (-1) (dblInt V μ m E f₁ f₂) := by
  induction k with
  | zero =>
    intro H r hr hinv hd hc hB
    refine ⟨H s₀, fun g => laurentCoeff_base ((hd g).continuousOn.continuousAt (ball_mem_nhds _ hr)),
      laurentCoeff_base (F := fun s => dblInt V μ m (H s) f₁ f₂) ?_⟩
    exact (dblInt_family hμ hm h₁ h₂ hinv hd hc hB).2.continuousOn.continuousAt (ball_mem_nhds _ hr)
  | succ k ih =>
    intro H r hr hinv hd hc hB
    obtain ⟨H', i1, i2, i3, i4, e⟩ := exists_div_family hr hinv hd hc hB
    obtain ⟨E, a, b⟩ := ih H' (r / 2) (half_pos hr) i1 i2 i3 i4
    refine ⟨E, fun g => laurentCoeff_step (c := H s₀ g) (.of_forall fun s => e s g) (a g),
      laurentCoeff_step (c := dblInt V μ m (H s₀) f₁ f₂) ?_ b⟩
    have c1 := (dblInt_family (f₁ := f₁) (f₂ := f₂) hμ hm h₁ h₂ hinv hd hc hB).1
    have c2 := (dblInt_family (f₁ := f₁) (f₂ := f₂) hμ hm h₁ h₂ i1 i2 i3 i4).1
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₀ (half_pos hr))] with s hs
    have e1 : H s = H s₀ + (s - s₀) • H' s := funext fun g => e s g
    have e2 := dblInt_smul (V := V) (μ := μ) (m := m) (E := H' s) (f₁ := f₁) (f₂ := f₂) (s - s₀) 1 1
    simp only [one_smul, map_one, mul_one] at e2
    rw [e1, dblInt_add (c1 s₀ (mem_ball_self hr)) (dblConv_smul (c2 s hs) _), e2]

theorem leftInv_of_eq {Φ : ℂ → GA D (dblSp V) → ℂ} (hinvE : ∀ s, LeftInv (GQ (dblSp V)) (eisCont V Φ s))
    {H : ℂ → GA D (dblSp V) → ℂ} {s₁ : ℂ} {r : ℝ} {k : ℕ} (hr : 0 < r)
    (e : ∀ s ∈ ball s₁ r, s ≠ s₁ → ∀ g, H s g = (s - s₁) ^ k * eisCont V Φ s g)
    (hd : ∀ g, DifferentiableOn ℂ (H · g) (ball s₁ r)) : ∀ s ∈ ball s₁ r, LeftInv (GQ (dblSp V)) (H s) := by
  intro s hs γ hγ g
  rcases eq_or_ne s s₁ with rfl | h0
  · have t1 := ((hd (γ * g)).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {s}ᶜ))
    have t2 := ((hd g).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {s}ᶜ))
    refine tendsto_nhds_unique t1 (t2.congr' ?_)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s hr)] with w h1 h2
    rw [e w h2 h1, e w h2 h1, hinvE w γ hγ g]
  · rw [e s hs h0, e s hs h0, hinvE s γ hγ g]

theorem dblInt_eisCont_eq {μ : (AE D)ˣ →* Circle} {m : Measure (GA D V)} {f₁ f₂ : GA D V → ℂ}
    {Φ : ℂ → GA D (dblSp V) → ℂ} {H : ℂ → GA D (dblSp V) → ℂ} {s₁ w : ℂ} {r : ℝ} {k : ℕ}
    (e : ∀ s ∈ ball s₁ r, s ≠ s₁ → ∀ g, H s g = (s - s₁) ^ k * eisCont V Φ s g) (h2 : w ∈ ball s₁ r) (h1 : w ≠ s₁) :
    dblInt V μ m (eisCont V Φ w) f₁ f₂ = dblInt V μ m (H w) f₁ f₂ / (w - s₁) ^ k := by
  have e1 : eisCont V Φ w = ((w - s₁) ^ k)⁻¹ • H w := by
    funext g
    rw [Pi.smul_apply, e w h2 h1 g, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ (sub_ne_zero.2 h1)), one_mul]
  have e2 := dblInt_smul (V := V) (μ := μ) (m := m) (E := H w) (f₁ := f₁) (f₂ := f₂) ((w - s₁) ^ k)⁻¹ 1 1
  simp only [one_smul, map_one, mul_one] at e2
  rw [e1, e2, div_eq_inv_mul]

theorem isMerExt_zeta {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ) {m : Measure (GA D V)} (hm : m.IsHaarMeasure)
    {Φ : ℂ → GA D (dblSp V) → ℂ} (hE : EisContinues V Φ)
    (ha : ∀ g, AnalyticOnNhd ℂ (eisSer V Φ g) (rightOf (V.rank / 2))) (hreg : ∀ s₀, ∃ k, EisRegularAt V Φ s₀ k)
    {f₁ f₂ : GA D V → ℂ} (h₁ : GlobalTheory.Grow.RapidDec V f₁) (h₂ : GlobalTheory.Grow.RapidDec V f₂) :
    IsMerExt (zeta V μ m Φ f₁ f₂) univ fun s => dblInt V μ m (eisCont V Φ s) f₁ f₂ := by
  have hinvE : ∀ s, LeftInv (GQ (dblSp V)) (eisCont V Φ s) := fun s => hE.1.leftInv_eisLaurent s 0
  refine ⟨isRightDomain_univ, fun s₁ _ => ?_, (V.rank : ℝ) / 2, fun s hs => ?_⟩
  · obtain ⟨k, r, H, hr, e, hd, hc, C, N, hb⟩ := hreg s₁
    have han : AnalyticAt ℂ (fun s => dblInt V μ m (H s) f₁ f₂) s₁ :=
      (dblInt_family hμ hm h₁ h₂ (leftInv_of_eq hinvE hr e hd) hd hc ⟨C, N, hb⟩).2.analyticAt (ball_mem_nhds _ hr)
    have hm1 : MeromorphicAt (fun s => dblInt V μ m (H s) f₁ f₂ / (s - s₁) ^ k) s₁ := by
      have : MeromorphicAt (fun s : ℂ => s - s₁) s₁ := (MeromorphicAt.id s₁).sub (MeromorphicAt.const _ _)
      exact han.meromorphicAt.fun_div (this.pow k)
    refine hm1.congr ?_
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₁ hr)] with w h1 h2
    exact (dblInt_eisCont_eq e h2 h1).symm
  · have : eisCont V Φ s = eis V (Φ s) := funext fun g => eqOn_cont (ha g) hs
    simp only [zeta, this]

theorem coeffAt_neg_one_zeta : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (m : Measure (GA D V)), m.IsHaarMeasure → ∀ (Φ : ℂ → GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisContinues V Φ → (∀ g, AnalyticOnNhd ℂ (GlobalTheory.Eis.eisSer V Φ g) (rightOf (V.rank / 2))) → (∀ s₀, ∃ k, GlobalTheory.Eis.EisRegularAt V Φ s₀ k) → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → GlobalTheory.Eis.IsZetaFamily V μ m Φ f₁ f₂ → ∀ (s₀ : ℂ) (E₁ : GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisCoeffAt V Φ s₀ (-1) E₁ → CoeffAt (GlobalTheory.Eis.zeta V μ m Φ f₁ f₂) s₀ (-1) (GlobalTheory.Eis.dblInt V μ m E₁ f₁ f₂) := by
  intro D V μ hμ m hm Φ hE ha hreg f₁ f₂ h₁ h₂ hZ s₀ E₁ hcoef
  have hinvE : ∀ s, LeftInv (GQ (dblSp V)) (eisCont V Φ s) := fun s => hE.1.leftInv_eisLaurent s 0
  obtain ⟨k, hk⟩ := hreg s₀
  obtain ⟨r, H, hr, e, hd, hc, C, N, hb⟩ := hk.succ
  obtain ⟨E, a, b⟩ := exists_coeff_family (m := m) (f₁ := f₁) (f₂ := f₂) hμ hm h₁ h₂ s₀ k H r hr
    (leftInv_of_eq hinvE hr e hd) hd hc ⟨C, N, hb⟩
  have hEE : E₁ = E := funext fun g => by
    obtain ⟨G, hG⟩ := hE.2 g
    have hx := hG.isExtAt (s₀ := s₀) trivial
    refine (hcoef.2 g).unique ⟨G, hx, (a g).congr ?_⟩
    filter_upwards [hx.cont_eventuallyEq, self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₀ hr)]
      with s h2 h3 h4
    have : (s - s₀) ^ (k + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 h3)
    rw [e s h4 h3 g, ← h2, mul_div_cancel_left₀ _ this]
    rfl
  rw [hEE]
  refine ⟨_, (isMerExt_zeta hμ hm hE ha hreg h₁ h₂).isExtAt trivial, b.congr ?_⟩
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₀ hr)] with w h1 h2
  exact (dblInt_eisCont_eq e h2 h1).symm

end GlobalTheory.CompanionTheory.Eis
