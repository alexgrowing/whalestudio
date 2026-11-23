import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAnalyticLogResolutionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MultiprojectivePointsNonemptyStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt

variable {K : Type} {J : K → Type}

theorem orb_symm {z z' : (Σ k, J k) → ℂ} (h : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit z z') :
    ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp only
  rw [← _root_.mul_assoc, inv_mul_cancel₀ (hc p.1), _root_.one_mul]

theorem orb_trans {z z' z'' : (Σ k, J k) → ℂ} (h : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit z z')
    (h' : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit z' z'') : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext p
  simp only [_root_.mul_assoc]

theorem orb_limit {α : Type} {F : Filter α} [F.NeBot] {a b : α → (Σ k, J k) → ℂ} {a₀ b₀ : (Σ k, J k) → ℂ}
    (ha : ∀ p, Tendsto (fun w => a w p) F (𝓝 (a₀ p))) (hb : ∀ p, Tendsto (fun w => b w p) F (𝓝 (b₀ p)))
    (h : ∀ᶠ w in F, ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (a w) (b w)) (h₀ : ∀ k, ∃ i, a₀ ⟨k, i⟩ ≠ 0)
    (h₁ : ∀ k, ∃ i, b₀ ⟨k, i⟩ ≠ 0) : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit a₀ b₀ := by
  choose ib hib using h₁
  choose ia hia using h₀
  have key : ∀ p : (Σ k, J k), a₀ p * b₀ ⟨p.1, ib p.1⟩ = a₀ ⟨p.1, ib p.1⟩ * b₀ p := by
    intro p
    have e1 : Tendsto (fun w => a w p * b w ⟨p.1, ib p.1⟩) F (𝓝 (a₀ p * b₀ ⟨p.1, ib p.1⟩)) :=
      (ha p).mul (hb _)
    have e2 : Tendsto (fun w => a w ⟨p.1, ib p.1⟩ * b w p) F (𝓝 (a₀ ⟨p.1, ib p.1⟩ * b₀ p)) :=
      (ha _).mul (hb p)
    refine tendsto_nhds_unique (e1.congr' ?_) e2
    filter_upwards [h] with w hw
    obtain ⟨c, -, hc⟩ := hw
    rw [hc]
    ring
  let c : K → ℂ := fun k => a₀ ⟨k, ib k⟩ / b₀ ⟨k, ib k⟩
  have hrel : ∀ p : (Σ k, J k), a₀ p = c p.1 * b₀ p := by
    intro p
    have hb0 := hib p.1
    simp only [c]
    field_simp
    rw [key p]
  refine ⟨c, fun k => ?_, funext hrel⟩
  intro hck
  apply hia k
  rw [hrel ⟨k, ia k⟩]
  simp [hck]

theorem continuousAt_of_holoOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : ReciprocityTheory.AnForm.M.FinHolAtlas e X)
    {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) {x : X} (hx : x ∈ U) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    simp only [Set.mem_preimage, (A.chart j).left_inv hj]
    exact hx
  have h1 : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j x) := (hg j _ hmem).continuousAt
  have h2 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ A.chart j) x :=
    h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

variable [Fintype K] [∀ k, Fintype (J k)]

theorem cxModel_of_res {P : Ideal (MRing J)} {d : ℕ} (R : AnLogRes P ⊤ d) (hne : (mcPts P).Nonempty) :
    Nonempty (CxModel P d) := by
  classical
  letI := R.top
  haveI := R.compact
  haveI := R.t2
  have htop : ∀ z, z ∉ mcPts (⊤ : Ideal (MRing J)) := by
    intro z hz
    have h1 := hz.2 1 Submodule.mem_top
    simp at h1
  have hex : ∀ z ∈ mcPts P, ∃ x, ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (R.lift x x) z :=
    fun z hz => R.surj z hz (htop z)
  have hmemU : ∀ x, R.lift x x ∈ mcPts P := fun x => R.mem x x (R.mem_U x)
  have hinj : ∀ x x', ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (R.lift x x) (R.lift x' x') → x = x' :=
    fun x x' h => R.inj x x' (htop _) h
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨x₀, -⟩ := hex z₀ hz₀
  let proj : ((Σ k, J k) → ℂ) → R.X := fun z =>
    if h : ∃ x, ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (R.lift x x) z then h.choose else x₀
  have hproj : ∀ z ∈ mcPts P, ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (R.lift (proj z) (proj z)) z := by
    intro z hz
    have h := hex z hz
    simp only [proj, dif_pos h]
    exact h.choose_spec
  have hproj_eq : ∀ z ∈ mcPts P, ∀ x, ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (R.lift x x) z → proj z = x := by
    intro z hz x hx
    exact hinj _ _ (orb_trans (hproj z hz) (orb_symm hx))
  have hlift : ∀ x y, y ∈ R.U x → proj (R.lift x y) = y := by
    intro x y hy
    exact hproj_eq _ (R.mem x y hy) y (R.compat y x y ⟨R.mem_U y, hy⟩)
  have hcont : ContinuousOn proj (mcPts P) := by
    intro z hz
    show Tendsto proj (𝓝[mcPts P] z) (𝓝 (proj z))
    refine isCompact_univ.tendsto_nhds_of_unique_mapClusterPt
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) ?_
    intro xs _ hxs
    have hG : (𝓝[mcPts P] z ⊓ comap proj (𝓝 xs)).NeBot := by
      rw [← Filter.map_neBot_iff proj, Filter.push_pull, inf_comm]
      exact hxs
    have hpx : Tendsto proj (𝓝[mcPts P] z ⊓ comap proj (𝓝 xs)) (𝓝 xs) :=
      tendsto_comap.mono_left inf_le_right
    have hid : Tendsto id (𝓝[mcPts P] z ⊓ comap proj (𝓝 xs)) (𝓝 z) :=
      tendsto_id.mono_left (inf_le_left.trans nhdsWithin_le_nhds)
    have hlim : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (R.lift xs xs) z := by
      refine orb_limit (F := 𝓝[mcPts P] z ⊓ comap proj (𝓝 xs))
        (a := fun w => R.lift xs (proj w)) (b := fun w => w) ?_ ?_ ?_ (hmemU xs).1 hz.1
      · intro p
        exact (continuousAt_of_holoOn R.A (R.holo xs p) (R.mem_U xs)).tendsto.comp hpx
      · intro p
        exact ((continuous_apply p).tendsto z).comp hid
      · have hU : ∀ᶠ w in 𝓝[mcPts P] z ⊓ comap proj (𝓝 xs), proj w ∈ R.U xs :=
          hpx ((R.isOpen_U xs).mem_nhds (R.mem_U xs))
        have hM : ∀ᶠ w in 𝓝[mcPts P] z ⊓ comap proj (𝓝 xs), w ∈ mcPts P :=
          Filter.mem_inf_of_left self_mem_nhdsWithin
        filter_upwards [hU, hM] with w hw hwm
        exact orb_trans (R.compat xs (proj w) (proj w) ⟨hw, R.mem_U _⟩) (hproj w hwm)
    exact (hproj_eq z hz xs hlim).symm
  have hfib : ∀ z ∈ mcPts P, ∀ z' ∈ mcPts P,
      proj z = proj z' ↔ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z' = torusSmul c z := by
    intro z hz z' hz'
    constructor
    · intro he
      have h1 := hproj z hz
      have h2 := hproj z' hz'
      rw [he] at h1
      obtain ⟨c, hc, hcz⟩ := orb_trans (orb_symm h2) h1
      exact ⟨c, hc, hcz⟩
    · rintro ⟨c, hc, hcz⟩
      have h3 : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit z' z := ⟨c, hc, hcz⟩
      exact (hproj_eq z' hz' (proj z) (orb_trans (hproj z hz) (orb_symm h3))).symm
  have hsurj : ∀ x, ∃ z ∈ mcPts P, proj z = x :=
    fun x => ⟨R.lift x x, hmemU x, hlift x x (R.mem_U x)⟩
  have hsec : ∀ x, ∃ U : Set R.X, IsOpen U ∧ x ∈ U ∧ ∃ s : R.X → (Σ k, J k) → ℂ,
      (∀ y ∈ U, s y ∈ mcPts P ∧ proj (s y) = y) ∧ ∀ p, R.A.HoloOn U fun y => s y p := by
    intro x
    exact ⟨R.U x, R.isOpen_U x, R.mem_U x, fun y => R.lift x y,
      fun y hy => ⟨R.mem x y hy, hlift x y hy⟩, fun p => R.holo x p⟩
  exact ⟨CxModel.mk R.X R.A proj hsurj hfib hcont hsec⟩

end LevelTowerAlt

theorem LevelTowerAlt.nonempty_component_model : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W), Nonempty (XModel D) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hy : ∀ k, ∃ i, D.y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := D.arith.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap]
    simp [h0]
  obtain ⟨R⟩ := GlobalTheory.T.exists_analytic_log_resolution K J Ω D.y D.n D.arith D.smoothGeneric
  exact LevelTowerAlt.cxModel_of_res R (GlobalTheory.T.multiprojective_points_nonempty K J Ω D.y hy)
