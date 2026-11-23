import Mathlib

open MeasureTheory

namespace GlobalTheory

open Filter Topology

theorem exists_measurable_invariant_index {G : Type} [Group G] [MetricSpace G]
    [ContinuousMul G] [MeasurableSpace G] [BorelSpace G] (L : Subgroup G) (y : ℕ → G)
    (r : ℝ) (Q : ℕ → G → Prop) (hQm : ∀ n, MeasurableSet {x | Q n x})
    (hQi : ∀ n, ∀ l ∈ L, ∀ x, Q n (l * x) ↔ Q n x)
    (hex : ∀ x, ∃ n, (∃ l ∈ L, dist (y n) (l * x) < r) ∧ Q n x) :
    ∃ s : G → ℕ, Measurable s ∧ (∀ x, ∃ l ∈ L, dist (y (s x)) (l * x) < r) ∧
      (∀ l ∈ L, ∀ x, s (l * x) = s x) ∧ ∀ x, Q (s x) x := by
  classical
  have hPm : ∀ n, MeasurableSet {x : G | (∃ l ∈ L, dist (y n) (l * x) < r) ∧ Q n x} := by
    intro n
    have hset : {x : G | ∃ l ∈ L, dist (y n) (l * x) < r} =
        ⋃ l : L, {x : G | dist (y n) ((l : G) * x) < r} := by
      ext x; simp
    have hopen : IsOpen {x : G | ∃ l ∈ L, dist (y n) (l * x) < r} := by
      rw [hset]
      exact isOpen_iUnion fun l =>
        isOpen_lt (continuous_const.dist (continuous_const.mul continuous_id)) continuous_const
    exact hopen.measurableSet.inter (hQm n)
  have hinv : ∀ l ∈ L, ∀ x n, ((∃ l' ∈ L, dist (y n) (l' * (l * x)) < r) ∧ Q n (l * x)) ↔
      ((∃ l' ∈ L, dist (y n) (l' * x) < r) ∧ Q n x) := by
    intro l hl x n
    refine and_congr ⟨?_, ?_⟩ (hQi n l hl x)
    · rintro ⟨m, hm, hd⟩
      exact ⟨m * l, L.mul_mem hm hl, by rwa [mul_assoc]⟩
    · rintro ⟨m, hm, hd⟩
      refine ⟨m * l⁻¹, L.mul_mem hm (L.inv_mem hl), ?_⟩
      simpa [mul_assoc] using hd
  refine ⟨fun x => Nat.find (hex x), measurable_find hex hPm, fun x => (Nat.find_spec (hex x)).1,
    fun l hl x => ?_, fun x => (Nat.find_spec (hex x)).2⟩
  exact le_antisymm (Nat.find_min' _ ((hinv l hl x _).2 (Nat.find_spec (hex x))))
    (Nat.find_min' _ ((hinv l hl x _).1 (Nat.find_spec (hex (l * x)))))

theorem exists_measurable_coset_section_metric {G : Type} [Group G] [MetricSpace G]
    [CompleteSpace G] [SecondCountableTopology G]
    [ContinuousMul G] [MeasurableSpace G] [BorelSpace G] (L : Subgroup G)
    (hL : IsClosed (L : Set G)) :
    ∃ σ : G → G, Measurable σ ∧ (∀ x, σ x * x⁻¹ ∈ L) ∧ ∀ l ∈ L, ∀ x, σ (l * x) = σ x := by
  classical
  obtain ⟨y, hy⟩ : ∃ y : ℕ → G, DenseRange y := TopologicalSpace.exists_dense_seq G
  let S : ℕ → Type := fun k => {s : G → ℕ // Measurable s ∧ (∀ l ∈ L, ∀ x, s (l * x) = s x) ∧
    ∀ x, ∃ l ∈ L, dist (y (s x)) (l * x) < (1 / 2 : ℝ) ^ k}
  have hy_meas : ∀ s : G → ℕ, Measurable s → Measurable (fun x => y (s x)) :=
    fun s hs => measurable_from_nat.comp hs

  have h0 : Nonempty (S 0) := by
    obtain ⟨s, hs, hclose, hinv, -⟩ := exists_measurable_invariant_index L y 1 (fun _ _ => True)
      (fun _ => MeasurableSet.univ) (fun _ _ _ _ => Iff.rfl) (fun x => by
        obtain ⟨n, hn⟩ := hy.exists_dist_lt x one_pos
        exact ⟨n, ⟨1, L.one_mem, by rw [one_mul, dist_comm]; exact hn⟩, trivial⟩)
    exact ⟨⟨s, hs, hinv, fun x => by simpa using hclose x⟩⟩

  have hstep : ∀ k (s : S k), ∃ s' : S (k + 1),
      ∀ x, dist (y (s'.1 x)) (y (s.1 x)) < 2 * (1 / 2 : ℝ) ^ k := by
    intro k s
    obtain ⟨s, hsm, hsi, hsc⟩ := s
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (k + 1) := by positivity
    have hhalf : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2 : ℝ) ^ k / 2 := by ring
    obtain ⟨s', hs'm, hclose, hinv, hQ⟩ := exists_measurable_invariant_index L y ((1 / 2 : ℝ) ^ (k + 1))
      (fun n x => dist (y n) (y (s x)) < 2 * (1 / 2 : ℝ) ^ k)
      (fun n => measurableSet_lt (measurable_const.dist (hy_meas s hsm)) measurable_const)
      (fun n l hl x => by simp only [hsi l hl x])
      (fun x => by
        obtain ⟨l, hl, hd⟩ := hsc x
        obtain ⟨n, hn⟩ := hy.exists_dist_lt (l * x) hpos
        refine ⟨n, ⟨l, hl, by rw [dist_comm]; exact hn⟩, ?_⟩
        have hk : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
        calc dist (y n) (y (s x)) ≤ dist (y n) (l * x) + dist (l * x) (y (s x)) := dist_triangle _ _ _
          _ < 2 * (1 / 2 : ℝ) ^ k := by
            rw [hhalf] at hn
            have e1 := dist_comm (y n) (l * x)
            have e2 := dist_comm (l * x) (y (s x))
            linarith)
    exact ⟨⟨s', hs'm, hinv, hclose⟩, hQ⟩
  choose step hstep using hstep
  let seq : (k : ℕ) → S k := fun k => Nat.rec (motive := S) h0.some (fun k s => step k s) k
  let f : ℕ → G → G := fun k x => y ((seq k).1 x)
  have hf_succ : ∀ k x, dist (f k x) (f (k + 1) x) ≤ 2 * (1 / 2 : ℝ) ^ k := fun k x => by
    rw [dist_comm]; exact (hstep k (seq k) x).le
  have hcauchy : ∀ x, CauchySeq (fun k => f k x) := fun x =>
    cauchySeq_of_le_geometric (1 / 2 : ℝ) 2 (by norm_num) (hf_succ · x)
  choose σ hσ using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  refine ⟨σ, ?_, ?_, ?_⟩
  · exact measurable_of_tendsto_metrizable (fun k => hy_meas _ (seq k).2.1) (tendsto_pi_nhds.2 hσ)
  · intro x
    have hC : IsClosed {z : G | z * x⁻¹ ∈ L} := hL.preimage (continuous_id.mul continuous_const)
    suffices h : σ x ∈ closure {z : G | z * x⁻¹ ∈ L} by rwa [hC.closure_eq] at h
    rw [Metric.mem_closure_iff]
    intro ε hε
    have h1 : ∀ᶠ k in atTop, dist (f k x) (σ x) < ε / 2 :=
      (hσ x).eventually (Metric.ball_mem_nhds _ (half_pos hε))
    have h2 : ∀ᶠ k in atTop, (1 / 2 : ℝ) ^ k < ε / 2 :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
        (gt_mem_nhds (half_pos hε))
    obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
    obtain ⟨l, hl, hd⟩ := (seq k).2.2.2 x
    refine ⟨l * x, by simpa using hl, ?_⟩
    calc dist (σ x) (l * x) ≤ dist (σ x) (f k x) + dist (f k x) (l * x) := dist_triangle _ _ _
      _ < ε := by rw [dist_comm] at hk1; change dist (f k x) (l * x) < _ at hd; linarith
  · intro l hl x
    have hfx : (fun k => f k (l * x)) = fun k => f k x := by
      funext k; simp only [f, (seq k).2.2.1 l hl x]
    have := hσ (l * x)
    rw [hfx] at this
    exact tendsto_nhds_unique this (hσ x)

theorem exists_measurable_coset_section (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G] (L : Subgroup G)
    (hL : IsClosed (L : Set G)) :
    ∃ σ : G → G, Measurable σ ∧ (∀ x, σ x * x⁻¹ ∈ L) ∧ ∀ l ∈ L, ∀ x, σ (l * x) = σ x := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable G
  exact exists_measurable_coset_section_metric L hL

end GlobalTheory
