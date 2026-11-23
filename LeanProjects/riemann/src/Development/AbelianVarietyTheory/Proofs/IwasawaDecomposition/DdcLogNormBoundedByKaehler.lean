import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open TopologicalSpace Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam

namespace GlobalTheory.ShFam.CurvBound

attribute [local instance] Over.cartesianMonoidalCategory

theorem eventually_abs_le {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {F G : X → E → ℝ} {x₀ : X} (hF : ∀ ξ, ContinuousAt (fun q : X × E => F q.1 q.2) (x₀, ξ))
    (hG : ∀ ξ, ContinuousAt (fun q : X × E => G q.1 q.2) (x₀, ξ))
    (sF : ∀ x (r : ℝ) ξ, F x (r • ξ) = r ^ 2 * F x ξ) (sG : ∀ x (r : ℝ) ξ, G x (r • ξ) = r ^ 2 * G x ξ)
    (hp : ∀ ξ, ξ ≠ 0 → 0 < G x₀ ξ) : ∃ K : ℝ, ∀ᶠ x in 𝓝 x₀, ∀ ξ, |F x ξ| ≤ K * G x ξ := by
  have hs : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere _ _
  have hne : ∀ ξ ∈ Metric.sphere (0 : E) 1, ξ ≠ 0 := fun ξ hξ h => by simp [h] at hξ
  have cF : Continuous (F x₀) := continuous_iff_continuousAt.2 fun ξ =>
    (hF ξ).comp (f := fun ξ => (x₀, ξ)) (by fun_prop)
  have cG : Continuous (G x₀) := continuous_iff_continuousAt.2 fun ξ =>
    (hG ξ).comp (f := fun ξ => (x₀, ξ)) (by fun_prop)
  obtain ⟨B, hB⟩ := hs.bddAbove_image (f := fun ξ => |F x₀ ξ| / G x₀ ξ)
    (cF.abs.continuousOn.div cG.continuousOn fun ξ hξ => (hp ξ (hne ξ hξ)).ne')
  refine ⟨B + 1, ?_⟩
  have h1 : ∀ᶠ x in 𝓝 x₀, ∀ ξ ∈ Metric.sphere (0 : E) 1, |F x ξ| < (B + 1) * G x ξ := by
    refine hs.eventually_forall_of_forall_eventually fun ξ hξ => ?_
    refine (hF ξ).abs.eventually_lt (continuousAt_const.mul (hG ξ)) ?_
    have h2 := hp ξ (hne ξ hξ)
    have h3 := (div_le_iff₀ h2).1 (hB ⟨ξ, hξ, rfl⟩)
    show |F x₀ ξ| < (B + 1) * G x₀ ξ
    linarith
  filter_upwards [h1] with x hx ξ
  rcases eq_or_ne ξ 0 with rfl | hξ
  · have e1 := sF x 0 0
    have e2 := sG x 0 0
    simp only [zero_smul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at e1 e2
    simp [e1, e2]
  · have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 hξ
    have h2 := hx (‖ξ‖⁻¹ • ξ) (by simp [norm_smul, hn])
    have e : ξ = ‖ξ‖ • (‖ξ‖⁻¹ • ξ) := by rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
    generalize ‖ξ‖⁻¹ • ξ = w at h2 e
    generalize ‖ξ‖ = r at e
    rw [e, sF, sG, abs_mul, abs_of_nonneg (sq_nonneg r), mul_left_comm]
    exact mul_le_mul_of_nonneg_left h2.le (sq_nonneg r)

open ReciprocityTheory.L2DbarEstimates in

theorem continuousAt_leviV {d : ℕ} {g : V d → ℂ} {x : V d} (hg : ContDiffAt ℝ 2 g x) (ξ : Fin d → ℂ) :
    ContinuousAt (fun q : V d × (Fin d → ℂ) => leviV d g q.1 q.2) (x, ξ) := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ g) x := hg.fderiv_right (by norm_num)
  have h2 : ∀ k, ContDiffAt ℝ 1 (wdb d k g) x := fun k =>
    ((h1.clm_apply contDiffAt_const).add (contDiffAt_const.mul (h1.clm_apply contDiffAt_const))).div_const 2
  have h3 : ∀ j k, ContinuousAt (wd d j (wdb d k g)) x := fun j k => by
    have h4 : ContinuousAt (fderiv ℝ (wdb d k g)) x := ((h2 k).fderiv_right (m := 0) (by norm_num)).continuousAt
    exact ((h4.clm_apply continuousAt_const).sub
      (continuousAt_const.mul (h4.clm_apply continuousAt_const))).div_const 2
  unfold leviV
  refine tendsto_finset_sum _ fun j _ => tendsto_finset_sum _ fun k _ => ?_
  refine ContinuousAt.mul (ContinuousAt.mul (ContinuousAt.comp (g := wd d j (wdb d k g)) (f := Prod.fst)
    (x := (x, ξ)) (h3 j k) continuousAt_fst) (by fun_prop)) ?_
  exact Complex.continuous_conj.continuousAt.comp (by fun_prop)

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}

theorem continuousAt_ddcForm {c : AlgChart p σ d} {f : CxPts p σ → ℝ} {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hf : ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y)) (ξ : Fin d → ℂ) :
    ContinuousAt (fun q : CxPts p σ × (Fin d → ℂ) => ddcForm f c q.1 q.2) (y, ξ) := by
  have h1 := continuousAt_leviV (Complex.ofRealCLM.contDiff.contDiffAt.comp _ hf) ξ
  have h2 : ContinuousAt (fun q : CxPts p σ × (Fin d → ℂ) => (c.e q.1, q.2)) (y, ξ) :=
    ((c.e.continuousAt hy).comp (f := Prod.fst) continuousAt_fst).prodMk continuousAt_snd
  exact (Complex.continuous_re.continuousAt.comp (h1.comp (f := fun q : CxPts p σ × (Fin d → ℂ) => (c.e q.1, q.2))
    h2)).div_const _

theorem ddcForm_smul (c : AlgChart p σ d) (f : CxPts p σ → ℝ) (y : CxPts p σ) (r : ℝ) (ξ : Fin d → ℂ) :
    ddcForm f c y (r • ξ) = r ^ 2 * ddcForm f c y ξ := by
  have : ∀ g v, ReciprocityTheory.L2DbarEstimates.leviV d g v (r • ξ) = ((r ^ 2 : ℝ) : ℂ) * ReciprocityTheory.L2DbarEstimates.leviV d g v ξ := fun g v => by
    simp only [ReciprocityTheory.L2DbarEstimates.leviV, Finset.mul_sum, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [ddcForm, ddcForm, AlgChart.levi, AlgChart.levi, this, Complex.re_ofReal_mul, mul_div_assoc]

theorem levi_eq {R : AnRead p σ d} {C : Closeds Y} {n f : CxPts p σ → ℝ} {V : Y.affineOpens} {t : Γ(Y, V.1)}
    (ht : (Scheme.IdealSheafData.vanishingIdeal C).ideal V = Ideal.span {t}) (hf : R.SmoothOn (ptsIn p σ V.1) f)
    (e : ∀ z ∈ ptsIn p σ V.1, n z ^ 2 = ‖ev p σ V.1 t z‖ ^ 2 * Real.exp (-f z)) {c : AlgChart p σ d} {y : CxPts p σ}
    (hc : y ∈ c.e.source) (hy : y ∈ ptsIn p σ V.1) (hC : ¬ LiesIn y C) (ξ : Fin d → ℂ) :
    c.levi (fun z => Real.exp 1 - Real.log (n z ^ 2)) y ξ = c.levi f y ξ := by
  have hS := (isOpen_not_liesIn (p := p) (σ := σ) C).inter (isOpen_ptsIn V.1)
  have h0 : ∀ z ∈ {z | ¬ LiesIn z C} ∩ ptsIn p σ V.1, ev p σ _ t z ≠ 0 :=
    fun z hz h0 => hz.1 ((ev_eq_zero_iff ht hz.2).1 h0)
  have hu := AnRead.holoOn_ev_of_subset (R := R) t (Set.inter_subset_right (s := {z | ¬ LiesIn z C}))
  have hl := hu.smoothOn_log hS h0
  have key : ∀ z ∈ {z | ¬ LiesIn z C} ∩ ptsIn p σ V.1,
      Real.exp 1 - Real.log (n z ^ 2) = f z + Real.exp 1 - Real.log (‖ev p σ _ t z‖ ^ 2) := fun z hz => by
    rw [e z hz.2, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 (h0 z hz))) (Real.exp_ne_zero _), Real.log_exp]
    ring
  have hs : R.SmoothOn ({z | ¬ LiesIn z C} ∩ ptsIn p σ V.1) fun z => Real.exp 1 - Real.log (n z ^ 2) :=
    AnRead.SmoothOn.congr (f := fun z => f z + Real.exp 1 - Real.log (‖ev p σ _ t z‖ ^ 2))
      (fun i => ((hf.mono Set.inter_subset_right i).add contDiffOn_const).sub (hl i)) key
  rw [← AnRead.levi_eq_of_add_log (g := fun z => f z + Real.exp 1) hS hs hu h0
    (fun z hz => by rw [key z hz, sub_add_cancel]) hc ⟨hC, hy⟩,
    AlgChart.levi_add (hf.contDiffAt_two (isOpen_ptsIn _) hc hy) contDiffAt_const]
  have : c.levi (fun _ => Real.exp 1) y ξ = 0 := by
    have : ∀ j, ReciprocityTheory.L2DbarEstimates.wdb d j (fun _ => ((Real.exp 1 : ℝ) : ℂ)) = fun _ => 0 := fun j => by
      funext v
      simp [ReciprocityTheory.L2DbarEstimates.wdb]
    simp only [AlgChart.levi, ReciprocityTheory.L2DbarEstimates.leviV, this]
    simp [ReciprocityTheory.L2DbarEstimates.wd]
  rw [this, add_zero]

theorem eventually_bound {R : AnRead p σ d} {C : Closeds Y} {n : CxPts p σ → ℝ} {a : ChartForm p σ d}
    (hn : IsDivNorm R C n) (ha : IsKaehlerForm R a) (y₀ : CxPts p σ) : ∃ K : ℝ, ∀ᶠ y in 𝓝 y₀,
      ∀ c : AlgChart p σ d, y ∈ c.e.source → ¬ LiesIn y C → ∀ ξ,
        |ddcForm (fun z => Real.exp 1 - Real.log (n z ^ 2)) c y ξ| ≤ K * a c y ξ := by
  obtain ⟨V, t, f, hy, ht, hf, e⟩ := hn.2 y₀
  obtain ⟨W, φ, hW, ho, hs, eφ⟩ := ha.1 y₀
  obtain ⟨i, hi⟩ := R.cover y₀
  obtain ⟨K, hK⟩ := eventually_abs_le (F := ddcForm f (R.chart i)) (G := ddcForm φ (R.chart i))
    (continuousAt_ddcForm hi (hf.contDiffAt_two (isOpen_ptsIn _) hi hy))
    (continuousAt_ddcForm hi (hs.contDiffAt_two ho hi hW)) (ddcForm_smul _ _) (ddcForm_smul _ _)
    fun ξ hξ => (ha.2 _ _ hi ξ hξ).trans_eq (eφ _ _ hi hW ξ)
  refine ⟨K, ?_⟩
  filter_upwards [hK, (isOpen_ptsIn _).mem_nhds hy, ho.mem_nhds hW, (R.chart i).e.open_source.mem_nhds hi]
    with y h1 h2 h3 h4 c hc hC ξ
  rw [ddcForm, levi_eq ht hf e hc h2 hC, AlgChart.levi_trans hc h4 (hf.contDiffAt_two (isOpen_ptsIn _) h4 h2),
    ha.trans hc h4, eφ _ _ h4 h3]
  exact h1 _

theorem exists_bound : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d p]
    (σ : k →+* ℂ) (C : Closeds Y) (n : CxPts p σ → ℝ) (a : ChartForm p σ d), IsProjOver p →
    IsDivNorm (AnRead.all p σ d) C n → IsKaehlerForm (AnRead.all p σ d) a → ∃ K : ℝ, ∀ (c : AlgChart p σ d),
    ∀ y ∈ c.e.source, ¬ LiesIn y C → ∀ ξ,
      |ddcForm (fun z => Real.exp 1 - Real.log (n z ^ 2)) c y ξ| ≤ K * a c y ξ := by
  intro k _ Y p d _ σ C n a hp hn ha
  have := CxPts.compactSpace σ hp
  choose K hK using eventually_bound hn ha
  obtain ⟨s, -, hs⟩ := isCompact_univ.elim_nhds_subcover _ fun y _ => hK y
  refine ⟨∑ x ∈ s, |K x|, fun c y hy hC ξ => ?_⟩
  obtain ⟨x, hx, h⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
  have h0 : 0 ≤ a c y ξ := by
    rcases eq_or_ne ξ 0 with rfl | hξ
    · obtain ⟨W, φ, hW, -, -, e⟩ := ha.1 y
      have := ddcForm_smul c φ y 0 0
      rw [e c y hy hW]
      simp only [zero_smul] at this
      rw [this]
      simp
    · exact (ha.2 c y hy ξ hξ).le
  exact (h c hy hC ξ).trans (mul_le_mul_of_nonneg_right
    ((le_abs_self _).trans (Finset.single_le_sum (f := fun x => |K x|) (fun _ _ => abs_nonneg _) hx)) h0)

end GlobalTheory.ShFam.CurvBound
