import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsBergDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AParamStA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AParamStB

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem gaap_measurableSet_pts {J : Type} [Fintype J] (P : Ideal (MvPolynomial J ℤ)) :
    MeasurableSet (pts P) := by
  have : pts P = ({0}ᶜ : Set (J → ℂ)) ∩
      ⋂ f ∈ P, {z : J → ℂ | eval z (map (Int.castRingHom ℂ) f) = 0} := by
    ext z
    simp [pts, conePts]
  rw [this]
  refine (measurableSet_singleton 0).compl.inter (IsClosed.measurableSet ?_)
  exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval _) continuous_const

theorem gaap_mem_ball_add {y₀ y : Fin D → ℂ} {ρ₀ : ℝ} :
    y₀ + y ∈ Metric.ball y₀ ρ₀ ↔ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀ := by
  simp [Metric.mem_ball, dist_eq_norm]

theorem exists_isParam {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) {z₀ : Ix κ → ℂ} (hz₀ : z₀ ∈ pts (coordIdeal ℤ x)) :
    ∃ (ρ₀ : ℝ) (γ : (Fin D → ℂ) → Ix κ → ℂ), 0 < ρ₀ ∧
      IsParam (coordIdeal ℤ x) (Metric.ball 0 ρ₀) γ ∧ γ 0 = z₀ := by
  classical
  set P := coordIdeal ℤ x with hPdef
  obtain ⟨T, hT, hTd⟩ := hg.smooth z₀ hz₀
  obtain ⟨-, ⟨hprime, -, -⟩, hhor, hdim⟩ := hg.arith
  haveI : P.IsPrime := hprime
  have hTle : D + 1 ≤ Fintype.card (Ix κ) := by
    rw [← hTd, ← Module.finrank_fintype_fun_eq_card ℂ]
    exact Submodule.finrank_le T
  set c := Fintype.card (Ix κ) - (D + 1) with hc
  let e : Ix κ ≃ Fin (D + 1 + c) := Fintype.equivFinOfCardEq (by omega)
  have hhor' : ∀ m : ℤ, (C m : MvPolynomial (Ix κ) ℤ) ∈ P → m = 0 := by
    intro m hm
    have : m ∈ P.comap (C : ℤ →+* MvPolynomial (Ix κ) ℤ) := hm
    rw [hhor] at this
    exact (Submodule.mem_bot ℤ).1 this
  have hdim' : ringKrullDim (MvPolynomial (Ix κ) ℤ ⧸ P) = ((D + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    convert hdim using 3
    simp
  obtain ⟨f, hfP, hli⟩ := gbap_indep_grads e P z₀ T hT hTd
  obtain ⟨F, h, hFli, hph, hiff⟩ := gbap_cut e P hhor' hdim' z₀ hz₀.2 f hfP hli
  set p' : Fin (D + 1 + c) → ℂ := fun j => z₀ (e.symm j) with hp'
  set Z' : Set (Fin (D + 1 + c) → ℂ) := {w | (fun j => w (e j)) ∈ pts P} with hZ'
  have hψ0 : ∀ w : Fin (D + 1 + c) → ℂ, w ≠ 0 → (fun j => w (e j)) ≠ 0 := by
    intro w hw h0
    apply hw
    funext i
    have := congrFun h0 (e.symm i)
    simpa using this
  have hZc : ∀ w ∈ Z', ∀ t : ℂ, t ≠ 0 → t • w ∈ Z' := by
    intro w hw t ht
    exact gbap_smul_mem_pts x hw ht
  have hZ : ∀ w, w ≠ 0 → eval w h ≠ 0 → (w ∈ Z' ↔ ∀ i, eval w (F i) = 0) := by
    intro w hw hwh
    rw [hiff w hwh]
    exact ⟨fun H => H.2, fun H => ⟨hψ0 w hw, H⟩⟩
  have hp'e : (fun j => p' (e j)) = z₀ := by
    funext j
    simp [hp']
  have hp'Z : p' ∈ Z' := by
    show (fun j => p' (e j)) ∈ pts P
    rw [hp'e]
    exact hz₀
  have hp'0 : p' ≠ 0 := by
    intro h0
    apply hz₀.1
    rw [← hp'e, h0]
    rfl
  obtain ⟨ρ₀, γ', hρ₀, hγan, hγZ, ⟨O', q', hO', hq', hOeq, hOc, hqγ⟩, hγ0⟩ :=
    gbap_param_of_cut Z' hZc F h hZ p' hp'Z hp'0 hph (gbap_surj_of_li F p' hFli)
  refine ⟨ρ₀, fun y j => γ' y (e j), hρ₀, ⟨Metric.isOpen_ball, ?_, fun y hy => hγZ y hy,
    {z | (fun i => z (e.symm i)) ∈ O'}, fun z => q' (fun i => z (e.symm i)), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro y hy
    exact analyticAt_pi_iff.2 fun j => (gbap_analyticAt_apply (e j) _).comp (hγan y hy)
  · exact hO'.preimage (continuous_pi fun i => continuous_apply _)
  · intro z hz
    exact (hq' _ hz).comp (analyticAt_pi_iff.2 fun i => gbap_analyticAt_apply (e.symm i) z)
  · ext z
    have hzz : (fun j => (fun i => z (e.symm i)) (e j)) = z := by
      funext j
      simp
    constructor
    · rintro ⟨hzO, hzP⟩
      have : (fun i => z (e.symm i)) ∈ O' ∩ Z' := ⟨hzO, by
        show _ ∈ pts P
        rw [hzz]
        exact hzP⟩
      rw [hOeq] at this
      obtain ⟨y, hy, t, ht, hte⟩ := this
      refine ⟨y, hy, t, ht, ?_⟩
      funext j
      have := congrFun hte (e j)
      simpa using this
    · rintro ⟨y, hy, t, ht, rfl⟩
      have hmem : t • γ' y ∈ O' ∩ Z' := by
        rw [hOeq]
        exact ⟨y, hy, t, ht, rfl⟩
      have heq : (fun i => (t • fun j => γ' y (e j)) (e.symm i)) = t • γ' y := by
        funext i
        simp
      refine ⟨?_, ?_⟩
      · show (fun i => (t • fun j => γ' y (e j)) (e.symm i)) ∈ O'
        rw [heq]
        exact hmem.1
      · exact hmem.2
  · intro z hz t ht
    exact hOc _ hz t ht
  · intro y hy
    have : (fun i => γ' y (e (e.symm i))) = γ' y := by
      funext i
      simp
    show q' (fun i => γ' y (e (e.symm i))) = y
    rw [this]
    exact hqγ y hy
  · funext j
    show γ' 0 (e j) = z₀ j
    rw [hγ0]
    simp [hp']

theorem IsParam.translate {P : Ideal (MvPolynomial (Ix κ) ℤ)} {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → Ix κ → ℂ} (h : IsParam P U γ) (y₀ : Fin D → ℂ) {ρ₀ : ℝ}
    (hball : Metric.ball y₀ ρ₀ ⊆ U) :
    IsParam P (Metric.ball 0 ρ₀) fun y => γ (y₀ + y) := by
  obtain ⟨_, hd, hpts, O, q, hO, hq, hOeq, hsc, hqγ⟩ := h
  have hmaps : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, y₀ + y ∈ U := fun y hy =>
    hball (gaap_mem_ball_add.2 hy)
  have hγO : ∀ y ∈ U, γ y ∈ O := fun y hy => by
    have : γ y ∈ coneOver U γ := ⟨y, hy, 1, one_ne_zero, (one_smul ℂ _).symm⟩
    rw [← hOeq] at this
    exact this.1
  refine ⟨Metric.isOpen_ball, ?_, fun y hy => hpts _ (hmaps y hy),
    O ∩ q ⁻¹' Metric.ball y₀ ρ₀, fun z => q z - y₀,
    hq.continuousOn.isOpen_inter_preimage hO Metric.isOpen_ball,
    (hq.mono Set.inter_subset_left).sub analyticOnNhd_const, ?_, ?_, ?_⟩
  · exact hd.comp (analyticOnNhd_const.add analyticOnNhd_id) fun y hy => hmaps y hy
  · ext z
    constructor
    · rintro ⟨⟨hzO, hzq⟩, hzp⟩
      have hz : z ∈ coneOver U γ := hOeq ▸ ⟨hzO, hzp⟩
      obtain ⟨y, hyU, c, hc, rfl⟩ := hz
      have h1 : q (c • γ y) = y := by rw [(hsc _ (hγO y hyU) c hc).2, hqγ y hyU]
      have hy : y ∈ Metric.ball y₀ ρ₀ := by
        have := hzq
        simp only [Set.mem_preimage, h1] at this
        exact this
      refine ⟨y - y₀, ?_, c, hc, ?_⟩
      · rw [← gaap_mem_ball_add (y₀ := y₀), add_sub_cancel]
        exact hy
      · simp
    · rintro ⟨y, hy, c, hc, rfl⟩
      have hcone : c • γ (y₀ + y) ∈ coneOver U γ := ⟨y₀ + y, hmaps y hy, c, hc, rfl⟩
      rw [← hOeq] at hcone
      refine ⟨⟨hcone.1, ?_⟩, hcone.2⟩
      simp only [Set.mem_preimage]
      rw [(hsc _ (hγO _ (hmaps y hy)) c hc).2, hqγ _ (hmaps y hy)]
      exact gaap_mem_ball_add.2 hy
  · rintro z ⟨hzO, hzq⟩ c hc
    have := hsc z hzO c hc
    refine ⟨⟨this.1, ?_⟩, ?_⟩
    · simp only [Set.mem_preimage, this.2]
      exact hzq
    · simp only [this.2]
  · intro y hy
    simp only
    rw [hqγ _ (hmaps y hy), add_sub_cancel_left]

theorem gaap_setLIntegral_translate (y₀ : Fin D → ℂ) (ρ₀ : ℝ) (F : (Fin D → ℂ) → ENNReal) :
    ∫⁻ y in Metric.ball (0 : Fin D → ℂ) ρ₀, F (y₀ + y) = ∫⁻ y in Metric.ball y₀ ρ₀, F y := by
  have hpre : (fun y => y₀ + y) ⁻¹' Metric.ball y₀ ρ₀ = Metric.ball (0 : Fin D → ℂ) ρ₀ := by
    ext y
    exact gaap_mem_ball_add
  rw [← hpre]
  exact (measurePreserving_add_left volume y₀).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addLeft y₀) F _

theorem IsDensityFor.translate {P : Ideal (MvPolynomial (Ix κ) ℤ)} {μ : Measure (Ix κ → ℂ)}
    {U : Set (Fin D → ℂ)} {γ : (Fin D → ℂ) → Ix κ → ℂ} {ν : (Fin D → ℂ) → ℝ} (h : IsParam P U γ)
    (hν : IsDensityFor μ U γ ν) (y₀ : Fin D → ℂ) {ρ₀ : ℝ} (hball : Metric.ball y₀ ρ₀ ⊆ U) :
    IsDensityFor μ (Metric.ball 0 ρ₀) (fun y => γ (y₀ + y)) fun y => ν (y₀ + y) := by
  obtain ⟨hνc, hνpos, hνint⟩ := hν
  have hmaps : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, y₀ + y ∈ U := fun y hy =>
    hball (gaap_mem_ball_add.2 hy)
  refine ⟨hνc.comp (contDiffOn_const.add contDiffOn_id) (fun y hy => hmaps y hy),
    fun y hy => hνpos _ (hmaps y hy), ?_⟩
  intro g hg hg0 hgnn
  obtain ⟨_, _, _, O', q', hO', -, hO'eq, -, -⟩ := h.translate y₀ hball
  obtain ⟨hU, _, _, O, q, _, _, hOeq, hsc, hqγ⟩ := h
  have hγO : ∀ y ∈ U, γ y ∈ O := fun y hy => by
    have : γ y ∈ coneOver U γ := ⟨y, hy, 1, one_ne_zero, (one_smul ℂ _).symm⟩
    rw [← hOeq] at this
    exact this.1
  set S := coneOver (Metric.ball (0 : Fin D → ℂ) ρ₀) (fun y => γ (y₀ + y)) with hSdef
  have hSm : MeasurableSet S := by
    rw [← hO'eq]
    exact hO'.measurableSet.inter (gaap_measurableSet_pts P)
  have hSsub : S ⊆ coneOver U γ := by
    rintro z ⟨y, hy, c, hc, rfl⟩
    exact ⟨y₀ + y, hmaps y hy, c, hc, rfl⟩
  have hSsmul : ∀ (c : ℂ) (z : Ix κ → ℂ), c ≠ 0 → (c • z ∈ S ↔ z ∈ S) := by
    intro c z hc
    constructor
    · rintro ⟨y, hy, c', hc', he⟩
      refine ⟨y, hy, c⁻¹ * c', mul_ne_zero (inv_ne_zero hc) hc', ?_⟩
      rw [mul_smul, ← he, smul_smul, inv_mul_cancel₀ hc, one_smul]
    · rintro ⟨y, hy, c', hc', rfl⟩
      exact ⟨y, hy, c * c', mul_ne_zero hc hc', by rw [mul_smul]⟩
  have hγS : ∀ y ∈ U, (γ y ∈ S ↔ y ∈ Metric.ball y₀ ρ₀) := by
    intro y hyU
    constructor
    · rintro ⟨y', hy', c, hc, he⟩
      have h1 : q (γ y) = y₀ + y' := by
        rw [he, (hsc _ (hγO _ (hmaps y' hy')) c hc).2, hqγ _ (hmaps y' hy')]
      rw [hqγ y hyU] at h1
      rw [h1]
      exact gaap_mem_ball_add.2 hy'
    · intro hy
      refine ⟨y - y₀, ?_, 1, one_ne_zero, ?_⟩
      · rw [← gaap_mem_ball_add (y₀ := y₀), add_sub_cancel]
        exact hy
      · simp
  have key := hνint (S.indicator g) (hg.indicator hSm)
    (fun c z hc => by
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((hSsmul c z hc).2 hz), hg0 c z hc]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h' => hz ((hSsmul c z hc).1 h'))])
    (fun z => Set.indicator_nonneg (fun z _ => hgnn z) z)
  have hL : ∫⁻ z in coneOver U γ, ENNReal.ofReal (S.indicator g z) ∂μ =
      ∫⁻ z in S, ENNReal.ofReal (g z) ∂μ := by
    have : (fun z => ENNReal.ofReal (S.indicator g z)) = S.indicator (fun z => ENNReal.ofReal (g z)) := by
      funext z
      by_cases hz : z ∈ S <;> simp [hz]
    rw [this, setLIntegral_indicator hSm, Set.inter_eq_left.2 hSsub]
  have hR : ∫⁻ y in U, ENNReal.ofReal (S.indicator g (γ y) * ν y) =
      ∫⁻ y in Metric.ball y₀ ρ₀, ENNReal.ofReal (g (γ y) * ν y) := by
    rw [← Set.inter_eq_left.2 hball, ← setLIntegral_indicator Metric.isOpen_ball.measurableSet]
    refine setLIntegral_congr_fun hU.measurableSet (fun y hyU => ?_)
    by_cases hy : y ∈ Metric.ball y₀ ρ₀
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem ((hγS y hyU).2 hy)]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h' => hy ((hγS y hyU).1 h'))]
      simp
  rw [← hL, key, hR]
  exact (gaap_setLIntegral_translate y₀ ρ₀ (fun y => ENNReal.ofReal (g (γ y) * ν y))).symm

theorem exists_finite_param_cover {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)}
    {μ : Measure (Ix κ → ℂ)} (hg : IsGood D x m μ) :
    ∃ (N : ℕ) (U C : Fin N → Set (Fin D → ℂ)) (γ : Fin N → (Fin D → ℂ) → Ix κ → ℂ),
      (∀ a, IsParam (coordIdeal ℤ x) (U a) (γ a)) ∧ (∀ a, IsCompact (C a) ∧ C a ⊆ U a) ∧
      ∀ z ∈ pts (coordIdeal ℤ x), ∃ a, z ∈ coneOver (C a) (γ a) := by
  classical
  set P := coordIdeal ℤ x with hPdef
  set S := pts P ∩ Metric.sphere (0 : Ix κ → ℂ) 1 with hSdef
  have hS : IsCompact S := gbap_isCompact_pts_sphere P
  have hex : ∀ s : S, ∃ (ρ : ℝ) (γ : (Fin D → ℂ) → Ix κ → ℂ) (O : Set (Ix κ → ℂ)), 0 < ρ ∧
      IsParam P (Metric.ball 0 ρ) γ ∧ IsOpen O ∧ (s : Ix κ → ℂ) ∈ O ∧
      O ∩ pts P ⊆ coneOver (Metric.closedBall 0 (ρ / 2)) γ := by
    intro s
    obtain ⟨ρ, γ, hρ, hγ, h0⟩ := exists_isParam hg s.2.1
    have hsub : Metric.ball (0 : Fin D → ℂ) (ρ / 2) ⊆ Metric.ball 0 ρ :=
      Metric.ball_subset_ball (by linarith)
    obtain ⟨_, _, _, O, q, hO, _, hOeq, _, _⟩ := hγ.translate 0 hsub
    refine ⟨ρ, γ, O, hρ, hγ, hO, ?_, ?_⟩
    · have : (s : Ix κ → ℂ) ∈ coneOver (Metric.ball (0 : Fin D → ℂ) (ρ / 2)) fun y => γ (0 + y) :=
        ⟨0, Metric.mem_ball_self (by linarith), 1, one_ne_zero, by simp [h0]⟩
      rw [← hOeq] at this
      exact this.1
    · rw [hOeq]
      rintro z ⟨y, hy, c, hc, rfl⟩
      exact ⟨y, Metric.ball_subset_closedBall hy, c, hc, by simp⟩
  choose ρ γ O hρ hγ hO hsO hOsub using hex
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun s : S => O s) (fun s => hO s)
    (fun s hs => Set.mem_iUnion.2 ⟨⟨s, hs⟩, hsO _⟩)
  let e := t.equivFin
  refine ⟨t.card, fun a => Metric.ball 0 (ρ (e.symm a).1),
    fun a => Metric.closedBall 0 (ρ (e.symm a).1 / 2), fun a => γ (e.symm a).1, fun a => hγ _,
    fun a => ⟨isCompact_closedBall _ _,
      Metric.closedBall_subset_ball (by linarith [hρ (e.symm a).1])⟩, ?_⟩
  intro z hz
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz.1
  set r : ℂ := (‖z‖ : ℂ) with hr
  have hr0 : r ≠ 0 := by
    rw [hr]
    exact_mod_cast hn
  set s := r⁻¹ • z with hsdef
  have hsS : s ∈ S := by
    refine ⟨gbap_smul_mem_pts x hz (inv_ne_zero hr0), ?_⟩
    rw [mem_sphere_zero_iff_norm, hsdef, norm_smul, norm_inv, hr, Complex.norm_real,
      Real.norm_eq_abs, abs_norm, inv_mul_cancel₀ hn]
  obtain ⟨i, hit, hsi⟩ := Set.mem_iUnion₂.1 (ht hsS)
  have hsc := hOsub i ⟨hsi, hsS.1⟩
  refine ⟨e ⟨i, hit⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  obtain ⟨y, hy, c, hc, hce⟩ := hsc
  refine ⟨y, hy, r * c, mul_ne_zero hr0 hc, ?_⟩
  rw [mul_smul, ← hce, hsdef, smul_smul, mul_inv_cancel₀ hr0, one_smul]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
