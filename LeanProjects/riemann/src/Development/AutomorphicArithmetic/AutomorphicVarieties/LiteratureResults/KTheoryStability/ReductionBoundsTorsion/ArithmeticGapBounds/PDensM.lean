import Mathlib

namespace PositivityTheory.KB.SpectralGap.WordTransvectionCongruences

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace

theorem two_le_prod {L : Type*} [Field L] [NumberField L] (π : 𝓞 L) (hπ : ¬ IsUnit π) (h0 : π ≠ 0) :
    (2 : ℝ) ≤ ∏ w : InfinitePlace L, w (π : L) ^ w.mult := by
  have h2 : |(Algebra.norm ℚ (π : L))| ≠ 1 := by
    intro h
    apply hπ
    rw [NumberField.isUnit_iff_norm]
    simpa [RingOfIntegers.coe_norm] using h
  rw [NumberField.InfinitePlace.prod_eq_abs_norm, ← Algebra.coe_norm_int] at *
  have h1 : Algebra.norm ℤ π ≠ 0 := Algebra.norm_ne_zero_iff.mpr h0
  set n := Algebra.norm ℤ π
  have h3 : |n| ≠ 1 := by
    intro h
    apply h2
    exact_mod_cast h
  have h4 : 2 ≤ |n| := by
    have := abs_pos.mpr h1
    omega
  exact_mod_cast h4

theorem exists_small {L : Type*} [Field L] [NumberField L] (π : 𝓞 L) (hπ : ¬ IsUnit π) (h0 : π ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : 𝓞 L, y ≠ 0 ∧ ∃ k : ℕ, ∀ w : InfinitePlace L, w ((y : L) / (π : L) ^ k) < ε := by
  have hP := two_le_prod π hπ h0
  set P := ∏ w : InfinitePlace L, w (π : L) ^ w.mult with hPdef
  set E : ℝ := ∏ w : InfinitePlace L, ε ^ w.mult with hEdef
  have hE : 0 < E := Finset.prod_pos fun w _ => pow_pos hε _
  have hc : (0 : ℝ) < mixedEmbedding.convexBodyLTFactor L := by
    have := mixedEmbedding.convexBodyLTFactor_ne_zero L
    positivity
  have hB := mixedEmbedding.minkowskiBound_lt_top L 1
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt
    ((mixedEmbedding.minkowskiBound L 1).toReal / (mixedEmbedding.convexBodyLTFactor L * E))
    (by linarith : (1 : ℝ) < P)
  have hπw : ∀ w : InfinitePlace L, 0 < w (π : L) := fun w => by
    rw [InfinitePlace.pos_iff]
    exact_mod_cast h0
  let f : InfinitePlace L → NNReal := fun w => ⟨ε * w (π : L) ^ k, by have := hπw w; positivity⟩
  have hf : ((∏ w, f w ^ w.mult : NNReal) : ℝ) = E * P ^ k := by
    rw [NNReal.coe_prod, hEdef, hPdef, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    change (ε * w (π : L) ^ k) ^ w.mult = _
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k]
  obtain ⟨a, ha0, ha⟩ := mixedEmbedding.exists_ne_zero_mem_ringOfIntegers_lt L (f := f) (by
    rw [mixedEmbedding.convexBodyLT_volume, ← ENNReal.coe_mul]
    rw [← ENNReal.toReal_lt_toReal hB.ne ENNReal.coe_ne_top]
    rw [ENNReal.coe_toReal, NNReal.coe_mul, hf]
    rw [div_lt_iff₀ (by positivity)] at hk
    linarith)
  refine ⟨a, ha0, k, fun w => ?_⟩
  rw [map_div₀, map_pow, div_lt_iff₀ (pow_pos (hπw w) _)]
  exact ha w

theorem exists_near {L : Type*} [Field L] [NumberField L] [IsTotallyComplex L] :
    ∃ R : ℝ, ∀ v : InfinitePlace L → ℂ, ∃ a : 𝓞 L, ∀ w, ‖v w - w.embedding (a : L)‖ ≤ R := by
  classical
  set b := mixedEmbedding.latticeBasis L
  refine ⟨∑ i, ‖b i‖, fun v => ?_⟩
  let x : mixedEmbedding.mixedSpace L := (0, fun w => v w.1)
  have hm := (ZSpan.floor b x).2
  rw [mixedEmbedding.mem_span_latticeBasis] at hm
  obtain ⟨a, ha⟩ := hm
  refine ⟨a, fun w => ?_⟩
  have hw : w.IsComplex := IsTotallyComplex.isComplex w
  have hfr := ZSpan.norm_fract_le b x
  rw [ZSpan.fract_apply, ← ha] at hfr
  refine le_trans ?_ hfr
  refine le_trans ?_ (norm_snd_le _)
  refine le_trans (le_of_eq ?_) (norm_le_pi_norm _ ⟨w, hw⟩)
  simp [x, mixedEmbedding.mixedEmbedding_apply_isComplex]

theorem dense_pow {L : Type*} [Field L] [NumberField L] [IsTotallyComplex L] (π : 𝓞 L)
    (hπ : ¬ IsUnit π) (h0 : π ≠ 0) :
    Dense {z : InfinitePlace L → ℂ | ∃ t : 𝓞 L, ∃ k : ℕ,
      z = fun w => w.embedding ((t : L) / (π : L) ^ k)} := by
  obtain ⟨R, hR⟩ := exists_near (L := L)
  rw [Metric.dense_iff]
  intro z δ hδ
  have hε : 0 < δ / (|R| + 1) := by positivity
  obtain ⟨y, hy0, k, hyk⟩ := exists_small π hπ h0 hε
  set q : L := (y : L) / (π : L) ^ k with hqdef
  have hq : q ≠ 0 := div_ne_zero (by exact_mod_cast hy0) (pow_ne_zero _ (by exact_mod_cast h0))
  obtain ⟨a, ha⟩ := hR (fun w => z w / w.embedding q)
  refine ⟨fun w => w.embedding (((a * y : 𝓞 L) : L) / (π : L) ^ k), ?_, a * y, k, rfl⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hδ]
  intro w
  have heq : w.embedding q ≠ 0 := by
    rw [ne_eq, map_eq_zero]
    exact hq
  have hsplit : z w - w.embedding (((a * y : 𝓞 L) : L) / (π : L) ^ k)
      = (z w / w.embedding q - w.embedding (a : L)) * w.embedding q := by
    rw [show (((a * y : 𝓞 L) : L) / (π : L) ^ k) = (a : L) * q by
      rw [hqdef]; push_cast; ring]
    rw [map_mul, sub_mul, div_mul_cancel₀ _ heq]
  rw [dist_comm, dist_eq_norm, hsplit, norm_mul, InfinitePlace.norm_embedding_eq]
  have h1 := ha w
  have h2 := hyk w
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) h1
  have hwq : 0 ≤ w q := by positivity
  have h3 : ‖z w / w.embedding q - w.embedding (a : L)‖ * w q ≤ |R| * (δ / (|R| + 1)) :=
    calc ‖z w / w.embedding q - w.embedding (a : L)‖ * w q ≤ R * (δ / (|R| + 1)) :=
          mul_le_mul h1 h2.le hwq hR0
      _ = |R| * (δ / (|R| + 1)) := by rw [abs_of_nonneg hR0]
  have h4 : |R| * (δ / (|R| + 1)) < δ := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg R]
  linarith

end PositivityTheory.KB.SpectralGap.WordTransvectionCongruences
