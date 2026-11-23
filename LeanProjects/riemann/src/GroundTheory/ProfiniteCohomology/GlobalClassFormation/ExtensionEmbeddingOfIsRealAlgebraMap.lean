import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in

theorem apply_eq_abs_embedding_of_isReal {v : InfinitePlace K} (hv : v.IsReal) (x : K) :
    v x = |embedding_of_isReal hv x| := by
  rw [← norm_embedding_of_isReal hv x, Real.norm_eq_abs]

theorem exists_units_neg_iff_mem (S : Set {v : InfinitePlace K // v.IsReal}) :
    ∃ a : Kˣ, ∀ v : {v : InfinitePlace K // v.IsReal},
      (embedding_of_isReal v.2 (a : K) < 0 ↔ v ∈ S) ∧ (0 < embedding_of_isReal v.2 (a : K) ↔ v ∉ S) := by
  classical

  set c : InfinitePlace K → K := fun v => if h : v.IsReal then
    (if (⟨v, h⟩ : {v : InfinitePlace K // v.IsReal}) ∈ S then -1 else 1) else 1 with hcdef
  let t : (v : InfinitePlace K) → WithAbs v.1 := fun v => WithAbs.toAbs v.1 (c v)
  let U : Set ((v : InfinitePlace K) → WithAbs v.1) := Set.pi Set.univ fun v => Metric.ball (t v) 1
  have hU : IsOpen U := isOpen_set_pi Set.finite_univ fun v _ => Metric.isOpen_ball
  have htU : t ∈ U := fun v _ => Metric.mem_ball_self one_pos
  obtain ⟨x, hx⟩ := (InfinitePlace.denseRange_algebraMap_pi K).exists_mem_open hU ⟨t, htU⟩

  have hclose : ∀ v : InfinitePlace K, v (x - c v) < 1 := by
    intro v
    have h := hx v (Set.mem_univ v)
    rw [Metric.mem_ball, dist_eq_norm] at h
    exact h
  have hc : ∀ v : InfinitePlace K, v (c v) = 1 := by
    intro v
    rw [hcdef]
    show v.1 (if h : v.IsReal then (if (⟨v, h⟩ : {v : InfinitePlace K // v.IsReal}) ∈ S then -1 else 1)
      else 1) = 1
    split_ifs <;> simp only [AbsoluteValue.map_neg, AbsoluteValue.map_one]
  have hx0 : x ≠ 0 := by
    rintro rfl
    obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
    have := hclose v
    rw [zero_sub, show v (-c v) = v (c v) from v.1.map_neg _, hc] at this
    exact lt_irrefl _ this
  refine ⟨Units.mk0 x hx0, fun v => ?_⟩
  have h := hclose v.1
  rw [apply_eq_abs_embedding_of_isReal v.2, map_sub] at h
  have hcv : c v.1 = if v ∈ S then -1 else 1 := by rw [hcdef]; exact dif_pos v.2
  rw [hcv] at h
  rw [Units.val_mk0]
  by_cases hv : v ∈ S
  · rw [if_pos hv, map_neg, map_one, sub_neg_eq_add, abs_lt] at h
    exact ⟨⟨fun _ => hv, fun _ => by linarith [h.2]⟩, ⟨fun h' => by linarith [h.2], fun h' => absurd hv h'⟩⟩
  · rw [if_neg hv, map_one, abs_lt] at h
    exact ⟨⟨fun h' => by linarith [h.1], fun h' => absurd h' hv⟩, ⟨fun _ => hv, fun _ => by linarith [h.1]⟩⟩

theorem exists_units_sign (ε : {v : InfinitePlace K // v.IsReal} → ℤˣ) :
    ∃ a : Kˣ, ∀ v : {v : InfinitePlace K // v.IsReal},
      (SignType.sign (embedding_of_isReal v.2 (a : K)) : ℤ) = (ε v : ℤ) := by
  obtain ⟨a, ha⟩ := exists_units_neg_iff_mem {v | ε v = -1}
  refine ⟨a, fun v => ?_⟩
  rcases Int.units_eq_one_or (ε v) with hε | hε
  · have hpos : 0 < embedding_of_isReal v.2 (a : K) := (ha v).2.2 (by simp [hε])
    rw [sign_pos hpos, hε]
    rfl
  · have hneg : embedding_of_isReal v.2 (a : K) < 0 := (ha v).1.2 hε
    rw [sign_neg hneg, hε]
    rfl

omit [NumberField K] in

theorem extensionEmbeddingOfIsReal_algebraMap {v : InfinitePlace K} (hv : v.IsReal) (x : K) :
    Completion.extensionEmbeddingOfIsReal hv (algebraMap K v.Completion x) = embedding_of_isReal hv x :=
  Completion.extensionEmbeddingOfIsReal_coe hv (WithAbs.toAbs v.1 x)

theorem exists_units_neg_iff_mem_completion (S : Set {v : InfinitePlace K // v.IsReal}) :
    ∃ a : Kˣ, ∀ v : {v : InfinitePlace K // v.IsReal},
      (Completion.extensionEmbeddingOfIsReal v.2 (algebraMap K v.1.Completion (a : K)) < 0 ↔ v ∈ S) ∧
      (0 < Completion.extensionEmbeddingOfIsReal v.2 (algebraMap K v.1.Completion (a : K)) ↔ v ∉ S) := by
  obtain ⟨a, ha⟩ := exists_units_neg_iff_mem S
  exact ⟨a, fun v => by simpa only [extensionEmbeddingOfIsReal_algebraMap] using ha v⟩

end GroundTheory.ProfCoh
