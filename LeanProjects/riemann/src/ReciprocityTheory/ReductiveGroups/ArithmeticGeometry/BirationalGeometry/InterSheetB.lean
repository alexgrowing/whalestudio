import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterOsgood

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Metric Filter Topology

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}

def secSet (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (B : Set (Fin e → ℂ)) : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) :=
  {G | (∀ y ∉ B, G y = 0) ∧ DifferentiableOn ℂ G B ∧ ∀ y ∈ B, G y ∈ fibre P Ψ y}

theorem coincide_null (hA : OsgoodStatement) {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {c : Fin e → ℂ} {r : ℝ}
    {G G' : (Fin e → ℂ) → ((k : K) → ι k) → ℂ} (hG : G ∈ secSet P Ψ (ball c r))
    (hG' : G' ∈ secSet P Ψ (ball c r)) (hne : G ≠ G') :
    volume {y | y ∈ ball c r ∧ G y = G' y} = 0 := by
  obtain ⟨y0, hy0⟩ : ∃ y0, G y0 ≠ G' y0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (funext hcon)
  have hy0b : y0 ∈ ball c r := by
    by_contra hb
    exact hy0 (by rw [hG.1 y0 hb, hG'.1 y0 hb])
  obtain ⟨i, hi⟩ : ∃ i, G y0 i ≠ G' y0 i := by
    by_contra hcon
    push_neg at hcon
    exact hy0 (funext hcon)
  set f : (Fin e → ℂ) → ℂ := fun y => G y i - G' y i with hf
  have hdiff : DifferentiableOn ℂ f (ball c r) := by
    have h1 : DifferentiableOn ℂ (fun y => G y i) (ball c r) := fun y hy =>
      (differentiableWithinAt_pi.1 (hG.2.1 y hy)) i
    have h2 : DifferentiableOn ℂ (fun y => G' y i) (ball c r) := fun y hy =>
      (differentiableWithinAt_pi.1 (hG'.2.1 y hy)) i
    exact h1.sub h2
  have han : AnalyticOnNhd ℂ f (ball c r) := hA e (ball c r) f isOpen_ball hdiff
  have hnull := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_ball (convex_ball c r).isPreconnected han
    ⟨y0, hy0b, sub_ne_zero.2 hi⟩
  refine measure_mono_null ?_ hnull
  intro y hy
  exact ⟨hy.1, by simp [f, hy.2]⟩

theorem secSet_finite (hA : OsgoodStatement) {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (fibre P Ψ y).Finite)
    (c : Fin e → ℂ) {r : ℝ} (hr : 0 < r) : (secSet P Ψ (ball c r)).Finite := by
  by_contra hinf
  have hS : (secSet P Ψ (ball c r)).Infinite := hinf
  have key : ∀ m : ℕ, volume {y | y ∈ ball c r ∧ (fibre P Ψ y).ncard < m} = 0 := by
    intro m
    obtain ⟨F, hFS, hFc⟩ := hS.exists_subset_card_eq m
    have hnull : volume (⋃ G ∈ (↑F : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ)), ⋃ G' ∈ (↑F : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ)),
        {y | G ≠ G' ∧ y ∈ ball c r ∧ G y = G' y}) = 0 := by
      refine (measure_biUnion_null_iff (Finset.countable_toSet F)).2 fun G hG =>
        (measure_biUnion_null_iff (Finset.countable_toSet F)).2 fun G' hG' => ?_
      by_cases h : G = G'
      · simp [h]
      · refine measure_mono_null ?_ (coincide_null hA (hFS hG) (hFS hG') h)
        intro y hy
        exact ⟨hy.2.1, hy.2.2⟩
    refine measure_mono_null (fun y hy => ?_) hnull
    obtain ⟨hyb, hlt⟩ := hy
    by_contra hnot
    have hinj : Set.InjOn (fun G : ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) => G y) (↑F : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ)) := fun G hG G' hG' heq => by
      by_contra hne
      exact hnot (Set.mem_iUnion₂.2 ⟨G, hG, Set.mem_iUnion₂.2 ⟨G', hG', ⟨hne, hyb, heq⟩⟩⟩)
    have hmaps : Set.MapsTo (fun G : ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) => G y) (↑F : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ)) (fibre P Ψ y) := fun G hG => (hFS hG).2.2 y hyb
    have hle := Set.ncard_le_ncard_of_injOn (fun G : ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) => G y) hmaps hinj (hfin y)
    rw [Set.ncard_coe_finset, hFc] at hle
    omega
  have hcover : ball c r ⊆ ⋃ m : ℕ, {y | y ∈ ball c r ∧ (fibre P Ψ y).ncard < m} := fun y hy =>
    Set.mem_iUnion.2 ⟨(fibre P Ψ y).ncard + 1, hy, Nat.lt_succ_self _⟩
  have h0 : volume (ball c r) = 0 := measure_mono_null hcover (measure_iUnion_null key)
  exact (Metric.measure_ball_pos volume c hr).ne' h0

def badSet (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Set (Fin e → ℂ) :=
  {y | ∃ w γ γ', IsSheet P Ψ y w γ ∧ IsSheet P Ψ y w γ' ∧
    ¬ ((fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γ' y'))}

theorem segre_differentiableAt {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (hγ : DifferentiableAt ℂ γ y) : DifferentiableAt ℂ (fun y' => segre (γ y')) y := by
  rw [differentiableAt_pi]
  intro i
  simp only [segre]
  classical
  have key : ∀ s : Finset K, DifferentiableAt ℂ (fun x => ∏ k ∈ s, γ x ⟨k, i k⟩) y := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      simp only [Finset.prod_insert ha]
      exact ((differentiableAt_pi.1 hγ) ⟨a, i a⟩).mul ih
  exact key Finset.univ

theorem mem_secSet_of_sheet {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {B : Set (Fin e → ℂ)}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : ∀ y' ∈ B, DifferentiableAt ℂ γ y' ∧ γ y' ∈ mcPts P ∧ Ψ (segre (γ y')) = Fin.cons 1 y') :
    B.indicator (fun y' => segre (γ y')) ∈ secSet P Ψ B := by
  refine ⟨fun y hy => Set.indicator_of_notMem hy _, ?_, fun y hy => ?_⟩
  · have hd : DifferentiableOn ℂ (fun y' => segre (γ y')) B := fun y' hy' =>
      (segre_differentiableAt (h y' hy').1).differentiableWithinAt
    exact hd.congr (fun y' hy' => Set.indicator_of_mem hy' _)
  · rw [Set.indicator_of_mem hy]
    exact ⟨γ y, (h y hy).2.1, rfl, (h y hy).2.2⟩

theorem badSet_null (hA : OsgoodStatement) {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (fibre P Ψ y).Finite) :
    volume (badSet P Ψ) = 0 := by
  obtain ⟨Dc, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Fin e → ℂ)
  let S : (Fin e → ℂ) → ℚ → Set (Fin e → ℂ) := fun d q =>
    ⋃ G ∈ secSet P Ψ (ball d q), ⋃ G' ∈ secSet P Ψ (ball d q), {y | G ≠ G' ∧ y ∈ ball d (q : ℝ) ∧ G y = G' y}
  have hS : ∀ d q, volume (S d q) = 0 := by
    intro d q
    by_cases hq : (0 : ℝ) < q
    · have hfinS := secSet_finite hA hfin d hq
      refine (measure_biUnion_null_iff hfinS.countable).2 fun G hG =>
        (measure_biUnion_null_iff hfinS.countable).2 fun G' hG' => ?_
      by_cases h : G = G'
      · simp [h]
      · refine measure_mono_null ?_ (coincide_null hA hG hG' h)
        intro y hy
        exact ⟨hy.2.1, hy.2.2⟩
    · have hempty : ball d (q : ℝ) = ∅ := Metric.ball_eq_empty.2 (not_lt.1 hq)
      refine measure_mono_null ?_ measure_empty
      intro y hy
      simp only [S, Set.mem_iUnion] at hy
      obtain ⟨G, _, G', _, _, hyb, _⟩ := hy
      rw [hempty] at hyb
      exact hyb
  have hcount : volume (⋃ d ∈ Dc, ⋃ q : ℚ, S d q) = 0 :=
    (measure_biUnion_null_iff hDc).2 fun d _ => measure_iUnion_null fun q => hS d q
  refine measure_mono_null ?_ hcount
  intro y hy
  obtain ⟨w, γ, γ', ⟨hγw, hγev⟩, ⟨hγ'w, hγ'ev⟩, hne⟩ := hy
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hγev.and hγ'ev)
  obtain ⟨q, hq0, hqε⟩ : ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < ε / 2 := by
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn (half_pos hε)
    exact ⟨q, h1, h2⟩
  obtain ⟨d, hdD, hd⟩ := hDd.exists_mem_open isOpen_ball ⟨y, mem_ball_self hq0⟩
  have hdy : dist y d < q := by
    rw [dist_comm]
    exact hd
  have hyB : y ∈ ball d (q : ℝ) := by
    rw [mem_ball]
    exact hdy
  have hBsub : ball d (q : ℝ) ⊆ ball y ε := by
    intro y' hy'
    rw [mem_ball] at hy' ⊢
    calc dist y' y ≤ dist y' d + dist d y := dist_triangle _ _ _
      _ < q + q := by
        rw [dist_comm d y]
        exact add_lt_add hy' hdy
      _ < ε := by linarith
  have hG : (ball d (q : ℝ)).indicator (fun y' => segre (γ y')) ∈ secSet P Ψ (ball d (q : ℝ)) :=
    mem_secSet_of_sheet (fun y' hy' => (hball y' (hBsub hy')).1)
  have hG' : (ball d (q : ℝ)).indicator (fun y' => segre (γ' y')) ∈ secSet P Ψ (ball d (q : ℝ)) :=
    mem_secSet_of_sheet (fun y' hy' => (hball y' (hBsub hy')).2)
  refine Set.mem_iUnion₂.2 ⟨d, hdD, Set.mem_iUnion.2 ⟨q, Set.mem_iUnion₂.2 ⟨_, hG,
    Set.mem_iUnion₂.2 ⟨_, hG', ?_, hyB, ?_⟩⟩⟩⟩
  · intro heq
    apply hne
    filter_upwards [isOpen_ball.mem_nhds hyB] with y' hy'
    have h1 := congrFun heq y'
    simpa [Set.indicator_of_mem hy'] using h1
  · simp [Set.indicator_of_mem hyB, hγw, hγ'w]

end ReciprocityTheory.ChartRestriction.G.Geo
