import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartLocalAnalyticTrivializationStatement
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ContinuousAtOfHolo

namespace LevelTowerAlt.Charts

open Filter Topology Metric Set
open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart LocPot)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W} {M : XModel D}

structure IsChartOf (M : XModel D) (γ : (Fin D.n → ℂ) → (Σ k, J k) → ℂ)
    (e : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ)) : Prop where
  good : Good (mCoordIdeal D.y) γ
  target : e.target = ball 0 1
  symm : ∀ t, e.symm t = M.proj (γ t)
  compat : IsCompatChart M.atlas e

section One

variable {γ : (Fin D.n → ℂ) → (Σ k, J k) → ℂ} {e e' : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ)}

theorem IsChartOf.mem_ball (h : IsChartOf M γ e) {x : M.Xc} (hx : x ∈ e.source) : e x ∈ ball (0 : Fin D.n → ℂ) 1 :=
  h.target ▸ e.map_source hx

theorem IsChartOf.sec (h : IsChartOf M γ e) (x : M.Xc) (hx : x ∈ e.source) :
    γ (e x) ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (γ (e x)) = x :=
  ⟨h.good.mem _ (h.mem_ball hx), by rw [← h.symm, e.left_inv hx]⟩

theorem IsChartOf.holo (h : IsChartOf M γ e) (p : Σ k, J k) : M.atlas.HoloOn e.source fun x => γ (e x) p :=
  fun j y hy => analyticAt_pi_iff.1 ((h.good.an _ (h.mem_ball hy.2)).comp_of_eq ((h.compat j).1 y hy) rfl) p

theorem IsChartOf.q_smooth (h : IsChartOf M γ e) {ref : HermLine J} (hr : IsSmoothHerm ref) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => Real.log (ref.h (γ t))) e.target := by
  rw [h.target]
  exact (ContDiffOn.comp hr (h.good.an.contDiffOn_of_completeSpace.restrict_scalars ℝ)
    fun t ht => (h.good.mem t ht).1).log fun t ht => (ref.pos _ (h.good.mem t ht).1).ne'

theorem IsChartOf.closure_sub (h : IsChartOf M γ e) {r r' : ℝ} (hr : r < r') (hr' : r' ≤ 1) :
    closure (e.source ∩ e ⁻¹' ball 0 r) ⊆ e.source ∩ e ⁻¹' ball 0 r' := by
  have hs : closedBall (0 : Fin D.n → ℂ) r ⊆ e.target :=
    h.target ▸ closedBall_subset_ball (hr.trans_le hr')
  have hc : IsClosed (e.symm '' closedBall 0 r) :=
    ((isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn_symm.mono hs)).isClosed
  have hsub : e.source ∩ e ⁻¹' ball 0 r ⊆ e.symm '' closedBall 0 r :=
    fun x hx => ⟨e x, ball_subset_closedBall hx.2, e.left_inv hx.1⟩
  refine (closure_minimal hsub hc).trans ?_
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨e.map_target (hs ht), ?_⟩
  rw [mem_preimage, e.right_inv (hs ht)]
  exact closedBall_subset_ball hr ht

theorem IsChartOf.torus (h : IsChartOf M γ e) {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y))
    (hs : M.proj z ∈ e.source) : ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ γ (e (M.proj z)) = torusSmul c z :=
  (M.fibre _ hz _ (h.sec _ hs).1).1 (h.sec _ hs).2.symm

theorem IsChartOf.conj (h : IsChartOf M γ e) (h' : IsChartOf M (cj γ) e') {z : (Σ k, J k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal D.y)) (hs : M.proj z ∈ e.source) :
    M.proj (conjVec z) ∈ e'.source ∧ e' (M.proj (conjVec z)) = star (e (M.proj z)) := by
  obtain ⟨c, hc, he⟩ := h.torus hz hs
  have ht : star (e (M.proj z)) ∈ e'.target := h'.target ▸ star_mem_ball.2 (h.mem_ball hs)
  have key : M.proj (conjVec z) = e'.symm (star (e (M.proj z))) := by
    rw [h'.symm]
    refine (M.fibre _ (SncPiece.conj_mem hz) _ (h'.good.mem _ (h'.target ▸ ht))).2
      ⟨fun k => starRingEnd ℂ (c k), fun k => (map_ne_zero _).2 (hc k), ?_⟩
    simp only [cj, star_star, he, conj_torus]
  rw [key]
  exact ⟨e'.map_target ht, e'.right_inv ht⟩

theorem IsChartOf.conj_iff (h : IsChartOf M γ e) (h' : IsChartOf M (cj γ) e') {z : (Σ k, J k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal D.y)) : M.proj (conjVec z) ∈ e'.source ↔ M.proj z ∈ e.source := by
  refine ⟨fun hs => ?_, fun hs => (h.conj h' hz hs).1⟩
  have := (h'.conj (e' := e) (by rwa [cj_cj]) (SncPiece.conj_mem hz) hs).1
  rwa [SncPiece.conj_conj] at this

theorem IsChartOf.conj_ball (h : IsChartOf M γ e) (h' : IsChartOf M (cj γ) e') {z : (Σ k, J k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal D.y)) (r : ℝ) :
    M.proj (conjVec z) ∈ e'.source ∩ e' ⁻¹' ball 0 r ↔ M.proj z ∈ e.source ∩ e ⁻¹' ball 0 r := by
  rw [mem_inter_iff, mem_inter_iff, h.conj_iff h' hz]
  refine and_congr_right fun hs => ?_
  rw [mem_preimage, mem_preimage, (h.conj h' hz hs).2, star_mem_ball]

theorem IsChartOf.mem_bd (h : IsChartOf M γ e) {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y))
    (hs : M.proj z ∈ e.source) : z ∈ D.Bd ↔ γ (e (M.proj z)) ∈ D.Bd := by
  obtain ⟨c, hc, he⟩ := h.torus hz hs
  rw [he]
  refine ⟨fun hb => D.bd_torus z hb c hc, fun hb => ?_⟩
  have := D.bd_torus _ hb (fun k => (c k)⁻¹) fun k => inv_ne_zero (hc k)
  convert this using 1
  funext p
  simp [torusSmul, inv_mul_cancel_left₀ (hc p.1)]

end One

noncomputable def famCharts {N : ℕ} (γ : Fin N → (Fin D.n → ℂ) → (Σ k, J k) → ℂ)
    (e : Fin N → OpenPartialHomeomorph M.Xc (Fin D.n → ℂ)) (h : ∀ j, IsChartOf M (γ j) (e j))
    (hcov : ∀ x, ∃ j, x ∈ (e j).source ∩ e j ⁻¹' ball 0 (1 / 4)) (ref : HermLine J) (hr : IsSmoothHerm ref) :
    PotentialCharts M.atlas where
  N := N
  chart := e
  compat j := (h j).compat
  target_subset j := (h j).target.subset
  mid j := (e j).source ∩ e j ⁻¹' ball 0 (1 / 2)
  inner j := (e j).source ∩ e j ⁻¹' ball 0 (1 / 4)
  isOpen_mid j := (e j).isOpen_inter_preimage isOpen_ball
  isOpen_inner j := (e j).isOpen_inter_preimage isOpen_ball
  closure_inner j := (h j).closure_sub (by norm_num) (by norm_num)
  closure_mid j := ((h j).closure_sub (r' := 1) (by norm_num) le_rfl).trans inter_subset_left
  cover := hcov
  th :=
    { U := fun x => (e (hcov x).choose).source
      isOpen_U := fun _ => OpenPartialHomeomorph.open_source _
      mem_U := fun x => (hcov x).choose_spec.1
      φ := fun x y => Real.log (ref.h (γ (hcov x).choose (e (hcov x).choose y))) }
  th_pot := ⟨fun x k => ((h _).q_smooth hr).comp
      (((h _).compat k).1.contDiffOn_of_completeSpace.restrict_scalars ℝ)
      fun _ hy => OpenPartialHomeomorph.map_source _ hy.2,
    fun x x' y hy => sec_diff M ref (OpenPartialHomeomorph.open_source _) (OpenPartialHomeomorph.open_source _)
      (h _).sec (h _).sec (h _).holo (h _).holo hy⟩
  q j t := Real.log (ref.h (γ j t))
  q_smooth j := (h j).q_smooth hr
  q_th j x y hy := by
    obtain ⟨V, hV, hyV, G, hG, he⟩ := sec_diff M ref (e j).open_source (e (hcov x).choose).open_source
      (h _).sec (h _).sec (h _).holo (h _).holo ⟨hy.2, hy.1⟩
    exact ⟨V, hV, hyV, G, hG, fun z hz => he z ⟨⟨hz.1.1, hz.2⟩, hz.1.2⟩⟩

theorem good_chart (D : ComponentData II Ψ K J Ω W) (a : Fin D.nCharts) :
    Good (n := D.n) (mCoordIdeal D.y) (D.chart a).γ :=
  ⟨(D.chart a).analytic, (D.chart a).mem, (D.chart a).injective, GlobalTheory.T.chart_local_analytic_trivialization K J II Ψ Ω W D a⟩

theorem exists_eps {n : ℕ} (t₀ : Fin n → ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ 2 * ε ≤ r ∧ ε ≤ 1 / 4 ∧ ∀ i, t₀ i ≠ 0 → 2 * ε ≤ ‖t₀ i‖ := by
  have h : ∀ b : ℝ, 0 < b → ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 * ε ≤ b := fun b hb => by
    filter_upwards [Ioo_mem_nhdsGT (half_pos hb)] with ε hε
    linarith [hε.2]
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, t₀ i ≠ 0 → 2 * ε ≤ ‖t₀ i‖ := eventually_all.2 fun i => by
    by_cases hi : t₀ i = 0
    · exact Eventually.of_forall fun _ h0 => absurd hi h0
    · exact (h _ (norm_pos_iff.2 hi)).mono fun _ h1 _ => h1
  obtain ⟨ε, ⟨⟨h1, h3⟩, h4⟩, h5⟩ := ((((h r hr).and (h (1 / 2) (by norm_num))).and h2).and self_mem_nhdsWithin).exists
  exact ⟨ε, h5, h1, by linarith, h4⟩

end LevelTowerAlt.Charts

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

open LevelTowerAlt.Charts Metric Set in
theorem LevelTowerAlt.exists_potential_charts : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (ref : HermLine J) (r : Fin D.nCharts → (Fin D.n → ℂ) → ℝ), IsSmoothHerm ref → IsConjInvariantH ref → (∀ a t, 0 < r a t) → ∃ (P : GroundTheory.Heights₂.Heights.Regular.PotentialCharts M.atlas) (S : Fin P.N → Finset (Fin D.n)) (κ : Equiv.Perm (Fin P.N)), ThRef M ref P.th ∧ Adapted M P S ∧ FromSnc M P ∧ SymmCharts M P κ ∧ ∀ j, ∃ (a : Fin D.nCharts) (t₀ : Fin D.n → ℂ) (ε : ℝ), ‖t₀‖ ≤ 1 / 2 ∧ 0 < ε ∧ 2 * ε ≤ r a t₀ ∧ ε ≤ 1 / 4 ∧ ((∀ t ∈ (P.chart j).target, (P.chart j).symm t = M.proj ((D.chart a).γ (t₀ + (ε : ℂ) • t)) ∧ P.q j t = Real.log (ref.h ((D.chart a).γ (t₀ + (ε : ℂ) • t)))) ∨ ∀ t ∈ (P.chart j).target, (P.chart j).symm t = M.proj (conjVec ((D.chart a).γ (t₀ + (ε : ℂ) • star t))) ∧ P.q j t = Real.log (ref.h ((D.chart a).γ (t₀ + (ε : ℂ) • star t)))) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D M ref r hr hrc hr0
  classical
  let I := {p : Fin D.nCharts × (Fin D.n → ℂ) // ‖p.2‖ ≤ 1 / 2}
  choose ε hε0 hεr hε4 hεs using fun p : I => exists_eps p.1.2 (hr0 p.1.1 p.1.2)
  let g : I → (Fin D.n → ℂ) → (Σ k, J k) → ℂ := fun p t => (D.chart p.1.1).γ (p.1.2 + (ε p : ℂ) • t)
  let g' : I × Bool → (Fin D.n → ℂ) → (Σ k, J k) → ℂ := fun i => cond i.2 (cj (g i.1)) (g i.1)
  have hg : ∀ p, Good (mCoordIdeal D.y) (g p) := fun p => (good_chart D p.1.1).affine p.2 (hε0 p) (hε4 p)
  have hg' : ∀ i, Good (mCoordIdeal D.y) (g' i) := by
    rintro ⟨p, _ | _⟩
    exacts [hg p, (hg p).cj]
  have hg0 : ∀ p, g p 0 = (D.chart p.1.1).γ p.1.2 := fun p =>
    congrArg (D.chart p.1.1).γ (by rw [smul_zero, add_zero] : p.1.2 + (ε p : ℂ) • (0 : Fin D.n → ℂ) = p.1.2)
  choose E hEt hEs hEc using fun i => (hg' i).exists_chart M
  have hE : ∀ i, IsChartOf M (g' i) (E i) := fun i => ⟨hg' i, hEt i, hEs i, hEc i⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun p : I => (E (p, false)).source ∩ E (p, false) ⁻¹' ball 0 (1 / 4))
    (fun p => (E _).isOpen_inter_preimage isOpen_ball) (fun x _ => by
      obtain ⟨z, hz, rfl⟩ := M.surj x
      obtain ⟨a, t, ht, c, hc, e⟩ := D.chart_cover z hz
      have h0 : (0 : Fin D.n → ℂ) ∈ (E (⟨(a, t), ht⟩, false)).target := hEt _ ▸ mem_ball_self one_pos
      have e0 : g' (⟨(a, t), ht⟩, false) 0 = (D.chart a).γ t := hg0 ⟨(a, t), ht⟩
      have e1 : M.proj z = (E (⟨(a, t), ht⟩, false)).symm 0 := by
        rw [hEs]
        exact ((M.fibre _ ((hg' _).mem _ (mem_ball_self one_pos)) _ hz).2 ⟨c, hc, by rw [e0]; exact e⟩).symm
      refine mem_iUnion.2 ⟨⟨(a, t), ht⟩, ?_⟩
      rw [e1]
      refine ⟨(E _).map_target h0, ?_⟩
      rw [mem_preimage, (E _).right_inv h0]
      exact mem_ball_self (by norm_num))
  let sg := (Fintype.equivFin (F × Bool)).symm
  let ix : Fin (Fintype.card (F × Bool)) → I × Bool := fun j => ((sg j).1.1, (sg j).2)
  let fl : Equiv.Perm (F × Bool) := Equiv.prodCongr (Equiv.refl _) Equiv.boolNot
  let κ : Equiv.Perm (Fin (Fintype.card (F × Bool))) := (sg.trans fl).trans sg.symm
  have hκ : ∀ j, ix (κ j) = ((ix j).1, !(ix j).2) := fun j => by
    simp [ix, κ, fl, Equiv.boolNot]
  have hcj : ∀ j, g' (ix (κ j)) = cj (g' (ix j)) := fun j => by
    rw [hκ]
    rcases ix j with ⟨p, _ | _⟩
    · rfl
    · exact (cj_cj _).symm
  have hκκ : ∀ j, κ (κ j) = j := fun j => by
    have : ∀ x, fl (fl x) = x := fun x => by simp [fl, Equiv.boolNot, Prod.map]
    simp only [κ, Equiv.trans_apply, Equiv.apply_symm_apply, this, Equiv.symm_apply_apply]
  have hqq : ∀ j t, Real.log (ref.h (g' (ix (κ j)) (star t))) = Real.log (ref.h (g' (ix j) t)) := fun j t => by
    rw [hcj]
    simp only [cj, star_star]
    exact congrArg Real.log (hrc _)
  have hcov : ∀ x, ∃ j, x ∈ (E (ix j)).source ∩ E (ix j) ⁻¹' ball 0 (1 / 4) := fun x => by
    obtain ⟨p, hp, hx⟩ := mem_iUnion₂.1 (hF (mem_univ x))
    refine ⟨sg.symm (⟨p, hp⟩, false), ?_⟩
    simpa only [ix, Equiv.apply_symm_apply] using hx
  have hdis : ∀ i : I × Bool, (∀ t, g' i t = (D.chart i.1.1.1).γ (i.1.1.2 + (ε i.1 : ℂ) • t)) ∨
      ∀ t, g' i t = conjVec ((D.chart i.1.1.1).γ (i.1.1.2 + (ε i.1 : ℂ) • star t)) := by
    rintro ⟨p, _ | _⟩
    exacts [Or.inl fun _ => rfl, Or.inr fun _ => rfl]
  refine ⟨famCharts (fun j => g' (ix j)) (fun j => E (ix j)) (fun j => hE _) hcov ref hr,
    fun j => Finset.univ.filter fun i => (i : ℕ) < (D.chart (ix j).1.1.1).a ∧ (ix j).1.1.2 i = 0, κ,
    fun x y hy => ⟨_, OpenPartialHomeomorph.open_source _, hy, subset_rfl, _, (hE _).sec, (hE _).holo, fun _ => 0,
      fun _ => analyticOnNhd_const, fun _ _ => sub_self _⟩,
    fun j z hz hs => ?_, fun j => ⟨hEt _, (ix j).1.1.1, (ix j).1.1.2, ε (ix j).1, (ix j).1.2, hε0 _, hε4 _,
      fun i _ hi => hεs _ i hi, ?_⟩, ⟨hκκ, hqq, fun j z hz => ?_⟩,
    fun j => ⟨(ix j).1.1.1, (ix j).1.1.2, ε (ix j).1, (ix j).1.2, hε0 _, hεr _, hε4 _, ?_⟩⟩
  · have hs' : M.proj z ∈ (E (ix j)).source := hs
    have ht : ‖E (ix j) (M.proj z)‖ < 2 := (mem_ball_zero_iff.1 ((hE _).mem_ball hs')).trans one_lt_two
    change _ ↔ E (ix j) (M.proj z) ∈ _
    rw [(hE _).mem_bd hz hs']
    rcases hdis (ix j) with h | h
    · rw [h, SncPiece.mem_bd_iff D (ix j).1.2 (hε0 _) (hε4 _) (fun i _ hi => hεs _ i hi) ht]
      simp [ReciprocityTheory.AnForm.A.coordDiv]
    · rw [h, SncPiece.conj_mem_bd_iff, SncPiece.mem_bd_iff D (ix j).1.2 (hε0 _) (hε4 _) (fun i _ hi => hεs _ i hi)
        (by rwa [norm_star])]
      simp [ReciprocityTheory.AnForm.A.coordDiv]
  · exact (hdis (ix j)).imp (fun h t _ => (hEs _ t).trans (congrArg M.proj (h t)))
      fun h t _ => (hEs _ t).trans (congrArg M.proj (h t))
  · have h' : IsChartOf M (cj (g' (ix j))) (E (ix (κ j))) := hcj j ▸ hE (ix (κ j))
    exact ⟨(hE _).conj_iff h' hz, (hE _).conj_ball h' hz _, (hE _).conj_ball h' hz _,
      fun hs => ((hE _).conj h' hz hs).2⟩
  · refine (hdis (ix j)).imp (fun h t _ => ⟨(hEs _ t).trans (congrArg M.proj (h t)), ?_⟩)
      fun h t _ => ⟨(hEs _ t).trans (congrArg M.proj (h t)), ?_⟩
    · change Real.log (ref.h (g' (ix j) t)) = _
      rw [h]
    · change Real.log (ref.h (g' (ix j) t)) = _
      rw [h]
      exact congrArg Real.log (hrc _)
