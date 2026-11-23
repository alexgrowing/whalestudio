import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsLinearIndependentNormLeSuccMin

noncomputable section

open Module Submodule
open scoped InnerProductSpace

namespace GlobalTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_int_comb_norm_sub_sq_le (k : ℕ) (v : Fin k → E) {x : E}
    (hx : x ∈ span ℝ (Set.range v)) :
    ∃ w ∈ span ℤ (Set.range v), ‖x - w‖ ^ 2 ≤ (∑ i, ‖v i‖ ^ 2) / 4 := by
  induction k generalizing x with
  | zero =>
    refine ⟨0, zero_mem _, ?_⟩
    have : x = 0 := by simpa using hx
    simp [this]
  | succ k ih =>
    set U : Submodule ℝ E := span ℝ (Set.range (Fin.init v)) with hU
    have : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℝ).1 hx
    set a := c (Fin.last k)
    set u := v (Fin.last k)
    set y := ∑ i : Fin k, c i.castSucc • v i.castSucc with hy
    have hyU : y ∈ U := sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩)
    set p := U.starProjection u
    have hpU : p ∈ U := U.starProjection_apply_mem u
    have hq : u - p ∈ Uᗮ := U.sub_starProjection_mem_orthogonal u
    set t : ℝ := a - round a
    have ht : |t| ≤ 1 / 2 := abs_sub_round a
    obtain ⟨w, hw, hle⟩ := ih (Fin.init v) (x := y + t • p) (add_mem hyU (smul_mem _ _ hpU))
    have hwU : w ∈ U := span_subset_span ℤ ℝ _ hw
    refine ⟨w + round a • u, add_mem (span_mono ?_ hw) (smul_mem _ _ (subset_span ⟨_, rfl⟩)), ?_⟩
    · rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩
    have e : ∑ i, c i • v i - (w + round a • u) = (y + t • p - w) + t • (u - p) := by
      rw [Fin.sum_univ_castSucc, ← Int.cast_smul_eq_zsmul ℝ]
      simp only [t]; module
    have hz : y + t • p - w ∈ U := sub_mem (add_mem hyU (smul_mem _ _ hpU)) hwU
    have horth : ⟪y + t • p - w, t • (u - p)⟫_ℝ = 0 :=
      U.inner_right_of_mem_orthogonal hz (smul_mem _ _ hq)
    have hup : ‖u - p‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      have h1 : ⟪p, u - p⟫_ℝ = 0 := U.inner_right_of_mem_orthogonal hpU hq
      have h2 := norm_add_sq_real p (u - p)
      rw [add_sub_cancel, h1] at h2
      nlinarith [sq_nonneg ‖p‖]
    have ht2 : t ^ 2 ≤ 1 / 4 := by
      rw [← sq_abs]; nlinarith [abs_nonneg t]
    rw [e, norm_add_sq_real, horth, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      Fin.sum_univ_castSucc]
    have : t ^ 2 * ‖u - p‖ ^ 2 ≤ 1 / 4 * ‖u‖ ^ 2 :=
      mul_le_mul ht2 hup (sq_nonneg _) (by norm_num)
    have hle' : ‖y + t • p - w‖ ^ 2 ≤ (∑ i : Fin k, ‖v i.castSucc‖ ^ 2) / 4 := hle
    linarith

theorem exists_mem_span_int_norm_sub_sq_le {ι : Type*} [Fintype ι] (v : ι → E) {x : E}
    (hx : x ∈ span ℝ (Set.range v)) :
    ∃ w ∈ span ℤ (Set.range v), ‖x - w‖ ^ 2 ≤ (∑ i, ‖v i‖ ^ 2) / 4 := by
  let e := (Fintype.equivFin ι).symm
  have hr : Set.range (v ∘ e) = Set.range v := e.surjective.range_comp v
  obtain ⟨w, hw, h⟩ := exists_int_comb_norm_sub_sq_le _ (v ∘ e) (x := x) (by rwa [hr])
  refine ⟨w, by rwa [hr] at hw, h.trans_eq ?_⟩
  congr 1
  exact e.sum_comp (fun i => ‖v i‖ ^ 2)

theorem exists_mem_span_int_norm_sub_le {ι : Type*} [Fintype ι] (v : ι → E) {r : ℝ}
    (hr : ∀ i, ‖v i‖ ≤ r) {x : E} (hx : x ∈ span ℝ (Set.range v)) :
    ∃ w ∈ span ℤ (Set.range v), ‖x - w‖ ≤ √(Fintype.card ι) / 2 * r := by
  obtain ⟨w, hw, h⟩ := exists_mem_span_int_norm_sub_sq_le v hx
  refine ⟨w, hw, ?_⟩
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · have : ‖x - w‖ ^ 2 ≤ 0 := by simpa using h
    have h0 : ‖x - w‖ = 0 := by nlinarith [norm_nonneg (x - w)]
    simp [h0]
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hr i₀)
  have hs : ∑ i, ‖v i‖ ^ 2 ≤ Fintype.card ι * r ^ 2 := by
    calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : ι, r ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hr i) 2
      _ = Fintype.card ι * r ^ 2 := by simp
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  rw [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  linarith

variable {L : Submodule ℤ E}

theorem exists_mem_norm_sub_sq_le_of_mem_span {ι : Type*} [Fintype ι] {v : ι → E}
    (hL : ∀ i, v i ∈ L) {x : E} (hx : x ∈ span ℝ (Set.range v)) :
    ∃ w ∈ L, w ∈ span ℝ (Set.range v) ∧ ‖x - w‖ ^ 2 ≤ (∑ i, ‖v i‖ ^ 2) / 4 := by
  obtain ⟨w, hw, h⟩ := exists_mem_span_int_norm_sub_sq_le v hx
  exact ⟨w, span_le.2 (Set.range_subset_iff.2 hL) hw, span_subset_span ℤ ℝ _ hw, h⟩

theorem exists_mem_norm_sub_le_of_mem_span {ι : Type*} [Fintype ι] {v : ι → E} {r : ℝ}
    (hL : ∀ i, v i ∈ L) (hr : ∀ i, ‖v i‖ ≤ r) {x : E} (hx : x ∈ span ℝ (Set.range v)) :
    ∃ w ∈ L, w ∈ span ℝ (Set.range v) ∧ ‖x - w‖ ≤ √(Fintype.card ι) / 2 * r := by
  obtain ⟨w, hw, h⟩ := exists_mem_span_int_norm_sub_le v hr hx
  exact ⟨w, span_le.2 (Set.range_subset_iff.2 hL) hw, span_subset_span ℤ ℝ _ hw, h⟩

theorem coveringRadius_le_sqrt_sum {ι : Type*} [Fintype ι] {v : ι → E}
    (hv : span ℝ (Set.range v) = ⊤) (hL : ∀ i, v i ∈ L) :
    coveringRadius L ≤ √(∑ i, ‖v i‖ ^ 2) / 2 :=
  coveringRadius_le fun x => by
    obtain ⟨w, hw, -, h⟩ := exists_mem_norm_sub_sq_le_of_mem_span hL (x := x) (hv ▸ mem_top)
    refine ⟨w, hw, (abs_le_of_sq_le_sq' ?_ (by positivity)).2⟩
    rw [div_pow, Real.sq_sqrt (by positivity)]
    linarith

theorem coveringRadius_le_of_span_eq_top {ι : Type*} [Fintype ι] {v : ι → E} {r : ℝ}
    (hv : span ℝ (Set.range v) = ⊤) (hL : ∀ i, v i ∈ L) (hr : ∀ i, ‖v i‖ ≤ r) :
    coveringRadius L ≤ √(Fintype.card ι) / 2 * r :=
  coveringRadius_le fun x => by
    obtain ⟨w, hw, -, h⟩ := exists_mem_norm_sub_le_of_mem_span hL hr (x := x) (hv ▸ mem_top)
    exact ⟨w, hw, h⟩

theorem exists_mem_norm_sub_le_of_linearIndependent [FiniteDimensional ℝ E] {ι : Type*}
    [Fintype ι] {v : ι → E} {r : ℝ} (hv : LinearIndependent ℝ v)
    (hn : Fintype.card ι = finrank ℝ E) (hL : ∀ i, v i ∈ L) (hr : ∀ i, ‖v i‖ ≤ r) (x : E) :
    ∃ w ∈ L, ‖x - w‖ ≤ √(finrank ℝ E) / 2 * r := by
  have hs : span ℝ (Set.range v) = ⊤ :=
    eq_top_of_finrank_eq (by rw [finrank_span_eq_card hv, hn])
  obtain ⟨w, hw, -, h⟩ := exists_mem_norm_sub_le_of_mem_span hL hr (x := x) (hs ▸ mem_top)
  exact ⟨w, hw, hn ▸ h⟩

theorem coveringRadius_le_of_linearIndependent [FiniteDimensional ℝ E] {ι : Type*}
    [Fintype ι] {v : ι → E} {r : ℝ} (hv : LinearIndependent ℝ v)
    (hn : Fintype.card ι = finrank ℝ E) (hL : ∀ i, v i ∈ L) (hr : ∀ i, ‖v i‖ ≤ r) :
    coveringRadius L ≤ √(finrank ℝ E) / 2 * r :=
  coveringRadius_le (exists_mem_norm_sub_le_of_linearIndependent hv hn hL hr)

theorem exists_mem_norm_sub_le_lastMin_of_mem_span [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] {x : E} (hx : x ∈ span ℝ (L : Set E)) :
    ∃ w ∈ L, ‖x - w‖ ≤ √(finrank ℤ L) / 2 * lastMin L := by
  obtain ⟨v, hv, h⟩ := exists_linearIndependent_norm_le_succMin (L := L) le_rfl
  have hs : span ℝ (Set.range v) = span ℝ (L : Set E) :=
    eq_of_le_of_finrank_eq (span_mono (Set.range_subset_iff.2 fun i => (h i).1))
      (by rw [finrank_span_eq_card hv, Fintype.card_fin])
  obtain ⟨w, hw, -, h'⟩ := exists_mem_norm_sub_le_of_mem_span (fun i => (h i).1)
    (fun i => (h i).2) (x := x) (by rwa [hs])
  refine ⟨w, hw, ?_⟩
  rwa [Fintype.card_fin, ← lastMin, finrank_span_eq_finrank_int] at h'

theorem exists_mem_norm_sub_le_lastMin [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (x : E) :
    ∃ w ∈ L, ‖x - w‖ ≤ √(finrank ℝ E) / 2 * lastMin L := by
  have := exists_mem_norm_sub_le_lastMin_of_mem_span L (x := x)
    (by rw [IsZLattice.span_top]; exact mem_top)
  rwa [← finrank_span_eq_finrank_int, finrank_span_of_isZLattice] at this

theorem coveringRadius_le_lastMin [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    coveringRadius L ≤ √(finrank ℝ E) / 2 * lastMin L :=
  coveringRadius_le (exists_mem_norm_sub_le_lastMin L)

theorem coveringRadius_inSpan_le_lastMin [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] : coveringRadius (inSpan L) ≤ √(finrank ℤ L) / 2 * lastMin L := by
  have := coveringRadius_le_lastMin (inSpan L)
  rwa [lastMin_inSpan, finrank_span_eq_finrank_int] at this

theorem exists_closest_point {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (L : Submodule ℤ F) [DiscreteTopology L] (x : F) :
    ∃ w ∈ L, ∀ z ∈ L, ‖x - w‖ ≤ ‖x - z‖ := by
  obtain ⟨w, hw, h⟩ := exists_norm_sub_eq_infDist L x
  refine ⟨w, hw, fun z hz => ?_⟩
  rw [h, ← dist_eq_norm]
  exact Metric.infDist_le_dist_of_mem hz

theorem abs_two_mul_inner_le_of_norm_le {a y : E} (h₁ : ‖a‖ ≤ ‖a + y‖) (h₂ : ‖a‖ ≤ ‖a - y‖) :
    |2 * ⟪a, y⟫_ℝ| ≤ ‖y‖ ^ 2 := by
  have e₁ := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
  have e₂ := pow_le_pow_left₀ (norm_nonneg _) h₂ 2
  rw [norm_add_sq_real] at e₁
  rw [norm_sub_sq_real] at e₂
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem abs_two_mul_inner_le_of_closest {p w : E} (hw : w ∈ L)
    (h : ∀ z ∈ L, ‖p - w‖ ≤ ‖p - z‖) {y : E} (hy : y ∈ L) : |2 * ⟪p - w, y⟫_ℝ| ≤ ‖y‖ ^ 2 :=
  abs_two_mul_inner_le_of_norm_le
    ((h _ (sub_mem hw hy)).trans_eq (by congr 1; abel))
    ((h _ (add_mem hw hy)).trans_eq (by congr 1; abel))

theorem closest_iff_abs_two_mul_inner_le {p w : E} (hw : w ∈ L) :
    (∀ z ∈ L, ‖p - w‖ ≤ ‖p - z‖) ↔ ∀ y ∈ L, |2 * ⟪p - w, y⟫_ℝ| ≤ ‖y‖ ^ 2 := by
  refine ⟨fun h y hy => abs_two_mul_inner_le_of_closest hw h hy, fun h z hz => ?_⟩
  have h1 := (abs_le.1 (h _ (sub_mem hz hw))).2
  have h2 := norm_sub_sq_real (p - w) (z - w)
  rw [sub_sub_sub_cancel_right] at h2
  exact (abs_le_of_sq_le_sq' (by linarith) (norm_nonneg _)).2

theorem abs_two_mul_inner_le_of_norm_sub_eq_infDist {p w : E} (hw : w ∈ L)
    (h : ‖p - w‖ = Metric.infDist p (L : Set E)) {y : E} (hy : y ∈ L) :
    |2 * ⟪p - w, y⟫_ℝ| ≤ ‖y‖ ^ 2 :=
  abs_two_mul_inner_le_of_closest hw (fun z hz => by
    rw [h, ← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hz) hy

theorem exists_closest_point_inner [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] (p : E) :
    ∃ w ∈ L, (∀ z ∈ L, ‖p - w‖ ≤ ‖p - z‖) ∧ ‖p - w‖ ≤ ‖p‖ ∧
      ∀ y ∈ L, |2 * ⟪p - w, y⟫_ℝ| ≤ ‖y‖ ^ 2 := by
  obtain ⟨w, hw, h⟩ := exists_closest_point L p
  exact ⟨w, hw, h, by simpa using h 0 L.zero_mem,
    fun y hy => abs_two_mul_inner_le_of_closest hw h hy⟩

theorem coveringRadius_and_closest_point [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    (∀ (v : Fin (finrank ℝ E) → E) (r : ℝ), LinearIndependent ℝ v → (∀ i, v i ∈ L) →
      (∀ i, ‖v i‖ ≤ r) → ∀ x : E, ∃ w ∈ L, ‖x - w‖ ≤ √(finrank ℝ E) / 2 * r) ∧
    coveringRadius L ≤ √(finrank ℝ E) / 2 * lastMin L ∧
    (∀ x : E, ∃ w ∈ L, ∀ z ∈ L, ‖x - w‖ ≤ ‖x - z‖) ∧
    (∀ p : E, ∀ w ∈ L, (∀ z ∈ L, ‖p - w‖ ≤ ‖p - z‖) →
      ∀ y ∈ L, |2 * ⟪p - w, y⟫_ℝ| ≤ ‖y‖ ^ 2) :=
  ⟨fun _ _ hv hL hr => exists_mem_norm_sub_le_of_linearIndependent hv (Fintype.card_fin _) hL hr,
    coveringRadius_le_lastMin L, exists_closest_point L,
    fun _ _ hw h _ hy => abs_two_mul_inner_le_of_closest hw h hy⟩

end GlobalTheory
