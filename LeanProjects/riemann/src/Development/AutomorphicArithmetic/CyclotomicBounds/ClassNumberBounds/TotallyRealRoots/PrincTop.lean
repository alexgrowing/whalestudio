import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.UnitsMapSurjOfZmod

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem mem_princ_iff_norm {a : ℕ} {u : ℤ_[l]ˣ} :
    u ∈ princ l a ↔ ‖(u : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-a : ℤ) := by
  rw [mem_princ, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]

private theorem exists_princ_subset {s : Set ℤ_[l]ˣ} (hs : s ∈ nhds (1 : ℤ_[l]ˣ)) :
    ∃ a, (princ l a : Set ℤ_[l]ˣ) ⊆ s := by
  have h1 : Units.val '' s ∈ nhds ((1 : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.isOpenEmbedding_val.isOpenMap.image_mem_nhds hs
  simp only [Units.val_one] at h1
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h1
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨a, ha⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl)
  refine ⟨a, fun u hu => ?_⟩
  have hu' : (u : ℤ_[l]) ∈ Metric.ball (1 : ℤ_[l]) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    refine lt_of_le_of_lt (mem_princ_iff_norm.mp hu) ?_
    rwa [zpow_neg, zpow_natCast, ← inv_pow]
  obtain ⟨v, hv, hvu⟩ := hball hu'
  rwa [← Units.val_injective hvu]

theorem isOpen_princ (a : ℕ) : IsOpen (princ l a : Set ℤ_[l]ˣ) := by
  have hr : ((l : ℝ) ^ (-a : ℤ)) ≠ 0 :=
    (zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _).ne'
  have hset : (princ l a : Set ℤ_[l]ˣ) =
      Units.val ⁻¹' Metric.closedBall (1 : ℤ_[l]) ((l : ℝ) ^ (-a : ℤ)) := by
    ext u
    simp only [SetLike.mem_coe, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
    exact mem_princ_iff_norm
  have hopen : IsOpen (princ l a : Set ℤ_[l]ˣ) := by
    rw [hset]
    exact Units.continuous_val.isOpen_preimage _ (IsUltrametricDist.isOpen_closedBall _ hr)
  exact hopen

theorem isOpen_iff_princ_le (U : Subgroup ℤ_[l]ˣ) :
    IsOpen (U : Set ℤ_[l]ˣ) ↔ ∃ a, princ l a ≤ U := by
  constructor
  · intro h
    exact exists_princ_subset (h.mem_nhds U.one_mem)
  · rintro ⟨a, ha⟩
    exact Subgroup.isOpen_mono ha (isOpen_princ a)

theorem isOpen_iff_isClosed_finiteIndex (U : Subgroup ℤ_[l]ˣ) :
    IsOpen (U : Set ℤ_[l]ˣ) ↔ IsClosed (U : Set ℤ_[l]ˣ) ∧ U.FiniteIndex := by
  constructor
  · intro h
    refine ⟨U.isClosed_of_isOpen h, ?_⟩
    obtain ⟨a, ha⟩ := (isOpen_iff_princ_le U).mp h
    haveI : (princ l a).FiniteIndex := Subgroup.finiteIndex_ker (redPow l a)
    exact Subgroup.finiteIndex_of_le ha
  · rintro ⟨hc, hf⟩
    exact U.isOpen_of_isClosed_of_finiteIndex hc

theorem mem_of_isClosed {U : Subgroup ℤ_[l]ˣ} (hU : IsClosed (U : Set ℤ_[l]ˣ)) {x : ℤ_[l]ˣ}
    (h : ∀ b, ∃ u ∈ U, redPow l b u = redPow l b x) : x ∈ U := by
  rw [← SetLike.mem_coe, ← hU.closure_eq, mem_closure_iff_nhds]
  intro t ht
  have ht' : (fun y => x * y) ⁻¹' t ∈ nhds (1 : ℤ_[l]ˣ) := by
    apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
    simpa using ht
  obtain ⟨b, hb⟩ := exists_princ_subset ht'
  obtain ⟨u, hu, hux⟩ := h b
  have hmem : x⁻¹ * u ∈ princ l b := by
    show x⁻¹ * u ∈ (redPow l b).ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hux, inv_mul_cancel]
  refine ⟨u, ?_, hu⟩
  have := hb hmem
  simpa using this

end KStar.TotallyRealRoots
