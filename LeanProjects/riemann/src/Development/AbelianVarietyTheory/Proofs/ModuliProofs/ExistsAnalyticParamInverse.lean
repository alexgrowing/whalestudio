import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsLocalHomeomorphAddMonoidHomOfEventuallyEq
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOpenPartialHomeomorphAnalytic

namespace GlobalTheory

section ParamExp

open Metric Set Filter Asymptotics
open scoped Topology

variable {B V : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem exists_analytic_param_inverse {F : B × V → V} {b₀ : B} {A : V →L[ℂ] V}
    (hF : AnalyticAt ℂ F (b₀, 0)) (h0 : F (b₀, 0) = 0)
    (hA : HasFDerivAt (fun x => F (b₀, x)) A 0) (hinj : Function.Injective A) :
    ∃ G : B × V → V, AnalyticAt ℂ G (b₀, 0) ∧ G (b₀, 0) = 0 ∧
      ∀ᶠ q in 𝓝 ((b₀, 0) : B × V), G (q.1, F q) = q.2 ∧ F (q.1, G q) = q.2 := by
  have hd := hF.differentiableAt.hasFDerivAt
  have hA' : (fderiv ℂ F (b₀, 0)).comp (ContinuousLinearMap.inr ℂ B V) = A :=
    (HasFDerivAt.comp (f := fun x : V => (b₀, x)) (0 : V) hd
      (hasFDerivAt_prodMk_right b₀ (0 : V))).unique hA
  have hΨ : AnalyticAt ℂ (fun q : B × V => (q.1, F q)) (b₀, 0) := analyticAt_fst.prod hF
  have hdΨ : HasFDerivAt (fun q : B × V => (q.1, F q))
      ((ContinuousLinearMap.fst ℂ B V).prod (fderiv ℂ F (b₀, 0))) (b₀, 0) :=
    hasFDerivAt_fst.prodMk hd
  obtain ⟨Φ, hΦ, hs, ha⟩ := AffinePoints.exists_openPartialHomeomorph_analytic rfl hΨ (by
    rw [hdΨ.fderiv, injective_iff_map_eq_zero]
    rintro ⟨u, v⟩ huv
    have hu : u = 0 := congrArg Prod.fst huv
    subst hu
    have hv : A v = A 0 := by
      rw [map_zero, ← hA']
      exact congrArg Prod.snd huv
    rw [hinj hv]
    rfl)
  have hfix : Φ (b₀, 0) = (b₀, 0) := by rw [hΦ]; simp [h0]
  have ht : ((b₀, 0) : B × V) ∈ Φ.target := hfix ▸ Φ.map_source hs
  refine ⟨fun q => (Φ.symm q).2, analyticAt_snd.comp (ha _ ht), ?_, ?_⟩
  · have := Φ.left_inv hs
    rw [hfix] at this
    simp [this]
  · filter_upwards [Φ.eventually_left_inverse hs, Φ.eventually_right_inverse ht] with q h1 h2
    rw [hΦ] at h1 h2
    refine ⟨congrArg Prod.snd h1, ?_⟩
    have h3 : (Φ.symm q).1 = q.1 := by simpa using congrArg Prod.fst h2
    have h4 : F (Φ.symm q) = q.2 := congrArg Prod.snd h2
    rw [← h3]
    exact h4

omit [FiniteDimensional ℂ B] [FiniteDimensional ℂ V] in

theorem eventually_eq_zero_of_slices {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [CompleteSpace V] {F : B × W → V} {b₀ : B} (hF : AnalyticAt ℂ F (b₀, 0))
    (h : ∀ᶠ b in 𝓝 b₀, ∀ᶠ w in 𝓝 (0 : W), F (b, w) = 0) :
    ∀ᶠ q in 𝓝 ((b₀, 0) : B × W), F q = 0 := by
  obtain ⟨s, hs, hsa⟩ := Metric.eventually_nhds_iff_ball.mp hF.eventually_analyticAt
  rw [← ball_prod_same] at hsa
  filter_upwards [prod_mem_nhds (Filter.inter_mem h (ball_mem_nhds b₀ hs)) (ball_mem_nhds 0 hs)]
    with ⟨b, w⟩ ⟨⟨hb, hbs⟩, hw⟩
  have ha : AnalyticOnNhd ℂ (fun w => F (b, w)) (ball 0 s) := fun x hx =>
    AnalyticAt.comp (f := fun x : W => (b, x)) (hsa (b, x) ⟨hbs, hx⟩)
      (analyticAt_const.prod analyticAt_id)
  exact ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 s).isPreconnected
    (mem_ball_self hs) hb hw

theorem analyticAt_param_doublingLog {ε : B × V → V} {b₀ : B} (ha : AnalyticAt ℂ ε (b₀, 0))
    (h : ∀ᶠ b in 𝓝 b₀, (fun x => ε (b, x) - (2 : ℂ)⁻¹ • x) =O[𝓝 0] fun x => ‖x‖ ^ 2) :
    AnalyticAt ℂ (fun q : B × V => doublingLog (fun x => ε (q.1, x)) q.2) (b₀, 0) := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  set K : ℝ := ‖ε (b₀, 0)‖ + 1 with hK
  have hK0 : 0 < K := by positivity
  obtain ⟨s, hs, hsa⟩ := Metric.eventually_nhds_iff_ball.mp
    (ha.eventually_analyticAt.and ((ha.continuousAt.norm.eventually
      (gt_mem_nhds (lt_add_one _))).and ((continuous_fst.tendsto' (b₀, (0 : V)) b₀ rfl).eventually h)))
  rw [← ball_prod_same] at hsa
  set C : ℝ := 4 * K / s ^ 2 with hCdef
  have hC0 : 0 < C := by positivity
  have hCs : ∀ b ∈ ball b₀ s, ∀ x ∈ ball (0 : V) s, ‖ε (b, x) - (2 : ℂ)⁻¹ • x‖ ≤ C * ‖x‖ ^ 2 := by
    intro b hb x hx
    have hO := (hsa (b, 0) ⟨hb, mem_ball_self hs⟩).2.2
    have hd : DifferentiableOn ℂ (fun x => ε (b, x)) (ball 0 s) := fun y hy =>
      (DifferentiableAt.comp (f := fun x : V => (b, x)) y (hsa (b, y) ⟨hb, hy⟩).1.differentiableAt
        (by fun_prop)).differentiableWithinAt
    have h1 := SCV.norm_sub_sub_fderiv_le_of_ball hd
      (fun y hy => (hsa (b, y) ⟨hb, hy⟩).2.1.le) hx
    have h2 : ε (b, 0) = 0 := map_zero_of_isBigO_sq (f := fun x => ε (b, x))
      (L := (2 : ℂ)⁻¹ • ContinuousLinearMap.id ℂ V) hO
    have h3 := (hasFDerivAt_of_isBigO_sq (f := fun x => ε (b, x))
      (L := (2 : ℂ)⁻¹ • ContinuousLinearMap.id ℂ V) hO).fderiv
    rw [h3, h2, sub_zero, sub_zero] at h1
    refine le_of_le_of_eq h1 ?_
    rw [hCdef, div_pow]
    ring
  set r : ℝ := min s (1 / (8 * C)) with hr
  have hr0 : 0 < r := lt_min hs (by positivity)
  have hrs : r ≤ s := min_le_left _ _
  have hC : ∀ b ∈ ball b₀ s, ∀ x ∈ ball (0 : V) r, ‖ε (b, x) - (2 : ℂ)⁻¹ • x‖ ≤ C * ‖x‖ ^ 2 :=
    fun b hb x hx => hCs b hb x (ball_subset_ball hrs hx)
  have hc : ∀ b ∈ ball b₀ s, ∀ x ∈ ball (0 : V) r, ‖ε (b, x)‖ ≤ 5 / 8 * ‖x‖ := by
    intro b hb x hx
    have h1 := hC b hb x hx
    have h2 : ‖x‖ ≤ 1 / (8 * C) := (mem_ball_zero_iff.mp hx).le.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h2
    have h3 : ‖(2 : ℂ)⁻¹ • x‖ = 1 / 2 * ‖x‖ := by simp [norm_smul]
    have h4 := norm_le_norm_sub_add (ε (b, x)) ((2 : ℂ)⁻¹ • x)
    nlinarith [norm_nonneg x]
  have hd : ∀ j : ℕ, DifferentiableOn ℂ (fun q : B × V => (fun x => ε (q.1, x))^[j] q.2)
      (ball b₀ s ×ˢ ball 0 r) := by
    intro j
    induction j with
    | zero => exact differentiableOn_snd
    | succ j ih =>
      simp only [Function.iterate_succ_apply']
      intro q hq
      exact DifferentiableAt.comp_differentiableWithinAt
        (f := fun q : B × V => (q.1, (fun x => ε (q.1, x))^[j] q.2)) q
        (hsa (q.1, (fun x => ε (q.1, x))^[j] q.2) ⟨hq.1, ball_subset_ball hrs
          (iterate_mem_ball_of_contraction (hc q.1 hq.1) hq.2 j)⟩).1.differentiableAt
        (differentiableWithinAt_fst.prodMk (ih q hq))
  have hu : TendstoUniformlyOn
      (fun (j : ℕ) (q : B × V) => (2 : ℂ) ^ j • (fun x => ε (q.1, x))^[j] q.2)
      (fun q : B × V => doublingLog (fun x => ε (q.1, x)) q.2) atTop (ball b₀ s ×ˢ ball 0 r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    have h0 : Tendsto (fun j : ℕ => 64 / 7 * C * r ^ 2 * (25 / 32 : ℝ) ^ j) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (25 / 32 : ℝ)) (by norm_num)
        (by norm_num)).const_mul (64 / 7 * C * r ^ 2)
    filter_upwards [h0.eventually (gt_mem_nhds hη)] with j hj q hq
    rw [dist_comm]
    refine ((dist_doublingLog_le_of_contraction (hc q.1 hq.1) hC0.le (hC q.1 hq.1) hq.2 j).trans
      ?_).trans_lt hj
    have := (mem_ball_zero_iff.mp hq.2).le
    gcongr
  exact SCV.analyticAt_of_differentiableOn
    (SCV.differentiableOn_of_tendstoLocallyUniformlyOn (isOpen_ball.prod isOpen_ball)
      hu.tendstoLocallyUniformlyOn (Eventually.of_forall fun j => (hd j).const_smul _))
    (prod_mem_nhds (ball_mem_nhds b₀ hs) (ball_mem_nhds 0 hr0))

theorem exists_param_exp_log {b₀ : B} {M : B × V × V → V} (hM : AnalyticAt ℂ M (b₀, 0, 0))
    (hu : ∀ᶠ q : B × V in 𝓝 (b₀, 0), M (q.1, q.2, 0) = q.2)
    (hc : ∀ᶠ q : B × V × V in 𝓝 (b₀, 0, 0), M (q.1, q.2.1, q.2.2) = M (q.1, q.2.2, q.2.1))
    (hs : ∀ᶠ q : B × V × V × V in 𝓝 (b₀, 0, 0, 0),
      M (q.1, M (q.1, q.2.1, q.2.2.1), q.2.2.2) = M (q.1, q.2.1, M (q.1, q.2.2.1, q.2.2.2))) :
    ∃ E L : B × V → V, AnalyticAt ℂ E (b₀, 0) ∧ AnalyticAt ℂ L (b₀, 0) ∧
      (∀ᶠ b in 𝓝 b₀, E (b, 0) = 0 ∧
        HasFDerivAt (fun v => E (b, v)) (ContinuousLinearMap.id ℂ V) 0) ∧
      (∀ᶠ q : B × V in 𝓝 (b₀, 0), L (q.1, E q) = q.2 ∧ E (q.1, L q) = q.2) ∧
      ∀ᶠ q : B × V × V in 𝓝 (b₀, 0, 0),
        E (q.1, q.2.1 + q.2.2) = M (q.1, E (q.1, q.2.1), E (q.1, q.2.2)) := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  have hlaw : ∀ᶠ b in 𝓝 b₀, IsLocalCommGroupLaw fun p : V × V => M (b, p) := by
    filter_upwards [hM.eventually_analyticAt.curry_nhds, hu.curry_nhds, hc.curry_nhds,
      hs.curry_nhds] with b h1 h2 h3 h4
    exact IsLocalCommGroupLaw.of_unit
      (AnalyticAt.comp (f := fun p : V × V => (b, p)) h1.self_of_nhds
        (analyticAt_const.prod analyticAt_id)) h2 h3 h4
  have h₀ := hlaw.self_of_nhds
  have hM0 : M (b₀, 0, 0) = 0 := h₀.map_zero
  obtain ⟨ε, hεa, -, hε⟩ := exists_analytic_param_inverse
    (F := fun q : B × V => M (q.1, q.2, q.2)) (b₀ := b₀)
    (AnalyticAt.comp (f := fun q : B × V => (q.1, q.2, q.2)) hM
      (analyticAt_fst.prod (analyticAt_snd.prod analyticAt_snd))) hM0
    h₀.hasFDerivAt_doubling (IsLocalCommGroupLaw.twoEquiv V).injective
  have hε' : ∀ᶠ b in 𝓝 b₀, ∀ᶠ x in 𝓝 (0 : V), ε (b, M (b, x, x)) = x :=
    (hε.mono fun q hq => hq.1).curry_nhds
  set L : B × V → V := fun q => doublingLog (fun x => ε (q.1, x)) q.2 with hL
  have hLa : AnalyticAt ℂ L (b₀, 0) := analyticAt_param_doublingLog hεa (by
    filter_upwards [hlaw, hε'] with b h1 h2
    exact h1.isBigO_inverse (ε := fun x => ε (b, x)) h2)
  have hLb : ∀ᶠ b in 𝓝 b₀, L (b, 0) = 0 ∧
      HasFDerivAt (fun x => L (b, x)) (ContinuousLinearMap.id ℂ V) 0 ∧
      ∀ᶠ p in 𝓝 (0 : V × V), L (b, M (b, p)) - (L (b, p.1) + L (b, p.2)) = 0 := by
    filter_upwards [hlaw, hε'] with b h1 h2
    exact ⟨h1.doublingLog_zero (ε := fun x => ε (b, x)) h2,
      h1.hasFDerivAt_doublingLog (ε := fun x => ε (b, x)) h2,
      (h1.doublingLog_law (ε := fun x => ε (b, x)) h2).mono fun p hp => sub_eq_zero.mpr hp⟩
  have hadd : ∀ᶠ q : B × V × V in 𝓝 (b₀, 0),
      L (q.1, M q) - (L (q.1, q.2.1) + L (q.1, q.2.2)) = 0 := by
    refine eventually_eq_zero_of_slices
      (F := fun q : B × V × V => L (q.1, M q) - (L (q.1, q.2.1) + L (q.1, q.2.2))) ?_
      (hLb.mono fun b hb => hb.2.2)
    refine AnalyticAt.sub ?_ (AnalyticAt.add ?_ ?_)
    · exact AnalyticAt.comp_of_eq (f := fun q : B × V × V => (q.1, M q)) hLa
        (analyticAt_fst.prod hM) (Prod.ext rfl hM0)
    · exact AnalyticAt.comp_of_eq (f := fun q : B × V × V => (q.1, q.2.1)) hLa
        (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)) rfl
    · exact AnalyticAt.comp_of_eq (f := fun q : B × V × V => (q.1, q.2.2)) hLa
        (analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)) rfl
  obtain ⟨E, hEa, hE0, hE⟩ := exists_analytic_param_inverse hLa hLb.self_of_nhds.1
    hLb.self_of_nhds.2.1 Function.injective_id
  refine ⟨E, L, hEa, hLa, ?_, hE.mono fun q hq => hq.symm, ?_⟩
  · filter_upwards [hLb, hE.curry_nhds, hEa.eventually_analyticAt.curry_nhds] with b h1 h2 h3
    have h4 : E (b, 0) = 0 := by simpa [h1.1] using h2.self_of_nhds.1
    refine ⟨h4, ?_⟩
    have h5 : HasFDerivAt (fun v => E (b, v)) (fderiv ℂ (fun v => E (b, v)) 0) 0 :=
      (DifferentiableAt.comp (f := fun v : V => (b, v)) 0 h3.self_of_nhds.differentiableAt
        (by fun_prop)).hasFDerivAt
    have h6 := HasFDerivAt.comp (g := fun x => L (b, x)) (f := fun v => E (b, v)) 0
      (by simpa only [h4] using h1.2.1) h5
    have h7 := h6.unique ((hasFDerivAt_id (0 : V)).congr_of_eventuallyEq
      (h2.mono fun v hv => hv.2))
    rw [ContinuousLinearMap.id_comp] at h7
    rwa [h7] at h5
  · have tE : Tendsto E (𝓝 (b₀, 0)) (𝓝 0) := by
      simpa only [hE0] using hEa.continuousAt.tendsto
    have tM : Tendsto M (𝓝 (b₀, 0, 0)) (𝓝 0) := by
      simpa only [hM0] using hM.continuousAt.tendsto
    have t0 : Tendsto (fun q : B × V × V => q.1) (𝓝 (b₀, 0, 0)) (𝓝 b₀) :=
      continuous_fst.tendsto' _ _ rfl
    have t1 : Tendsto (fun q : B × V × V => (q.1, q.2.1)) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0)) :=
      Continuous.tendsto' (by fun_prop) _ _ rfl
    have t2 : Tendsto (fun q : B × V × V => (q.1, q.2.2)) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0)) :=
      Continuous.tendsto' (by fun_prop) _ _ rfl
    have t3 := t0.prodMk_nhds ((tE.comp t1).prodMk_nhds (tE.comp t2))
    filter_upwards [t3.eventually hadd, t1.eventually hE, t2.eventually hE,
      (t3.eventually (((continuous_fst.tendsto' _ _ rfl).prodMk_nhds tM).eventually hE))]
      with q h1 h2 h3 h4
    simp only [Function.comp] at h1 h2 h3 h4
    rw [sub_eq_zero, h2.2, h3.2] at h1
    rw [← h1, h4.1]

end ParamExp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem exists_param_exp_log_pi : ∀ (m g : ℕ) (b₀ : Fin m → ℂ) (M : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)), AnalyticAt ℂ M (b₀, 0, 0) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), M (q.1, q.2, 0) = q.2) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), M (q.1, q.2.1, q.2.2) = M (q.1, q.2.2, q.2.1)) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0, 0), M (q.1, M (q.1, q.2.1, q.2.2.1), q.2.2.2) = M (q.1, q.2.1, M (q.1, q.2.2.1, q.2.2.2))) → ∃ E L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ E (b₀, 0) ∧ AnalyticAt ℂ L (b₀, 0) ∧ (∀ᶠ b in nhds b₀, E (b, 0) = 0 ∧ HasFDerivAt (fun v => E (b, v)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧ (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), L (q.1, E q) = q.2 ∧ E (q.1, L q) = q.2) ∧ ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), E (q.1, q.2.1 + q.2.2) = M (q.1, E (q.1, q.2.1), E (q.1, q.2.2)) :=
  fun _ _ _ _ hM hu hc hs => exists_param_exp_log hM hu hc hs

end GlobalTheory
