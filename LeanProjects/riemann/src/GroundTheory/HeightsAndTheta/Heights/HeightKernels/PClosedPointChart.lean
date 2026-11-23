import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCurveCharts
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsClosedPointUnitSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace ClosedPointAffineChart

variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')

omit [Fintype T] in

theorem ratio_mem (t u : T) : y ⟨(), u⟩ / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) :=
  Algebra.subset_adjoin ⟨⟨(), u⟩, rfl⟩

omit [Fintype T] in

theorem mem_chart_of_mem_curveRing {b : K'} (hb : b ∈ curveRing y) (t : T) (ht : y ⟨(), t⟩ ≠ 0) :
    b ∈ chartRingZ y (fun _ => t) :=
  mem_curveRing.mp hb (fun _ => t) (fun _ => ht)

omit [Fintype T] in

theorem mem_curveRing_of_forall {b : K'}
    (h : ∀ t : T, y ⟨(), t⟩ ≠ 0 → b ∈ chartRingZ y (fun _ => t)) : b ∈ curveRing y := by
  rw [mem_curveRing]
  intro c hc
  have hc' : c = fun _ => c () := funext fun u => by cases u; rfl
  have h1 := h (c ()) (hc ())
  rwa [← hc'] at h1

omit [Fintype T] in

theorem div_pow_mem_of_mem_chartLat {e : ℕ} {g : K'} (hg : g ∈ chartLat y 1 e) (t : T)
    (ht : y ⟨(), t⟩ ≠ 0) : g / y ⟨(), t⟩ ^ e ∈ chartRingZ y (fun _ => t) := by
  have h : g * ∏ k : Unit, y ⟨k, t⟩ ^ (-((e : ℤ) * (1 : Unit → ℤ) k)) ∈ chartRingZ y (fun _ => t) :=
    hg (fun _ => t) (fun _ => ht)
  simpa [zpow_neg, zpow_natCast, div_eq_mul_inv] using h

omit [Fintype T] in

theorem exists_mul_inv_mem {m : Ideal (curveRing y)} [m.IsPrime] {e : ℕ} {g : K'} (hg0 : g ≠ 0)
    (hgL : g ∈ chartLat y 1 e)
    (hW : ∀ W : ValuationSubring K', (∀ b : curveRing y, (b : K') ∈ W) →
      (∀ b : curveRing y, b ∉ m → W.valuation (b : K') = 1) → ∀ u : T, y ⟨(), u⟩ ^ e / g ∈ W)
    (t : T) (ht : y ⟨(), t⟩ ≠ 0) :
    ∃ s : curveRing y, s ∉ m ∧ (s : K') * (y ⟨(), t⟩ ^ e / g) ∈ chartRingZ y (fun _ => t) := by
  by_contra hcon
  push Not at hcon
  let R : Subring K' := (chartRingZ y (fun _ => t)).toSubring
  have hBR : curveRing y ≤ R := fun b hb => mem_chart_of_mem_curveRing y hb t ht
  let S' : Submonoid R := m.primeCompl.map (Subring.inclusion hBR)
  let z : R := ⟨g / y ⟨(), t⟩ ^ e, div_pow_mem_of_mem_chartLat y hgL t ht⟩
  have hyt : y ⟨(), t⟩ ^ e ≠ 0 := pow_ne_zero _ ht
  have hdisj : Disjoint ((Ideal.span {z} : Ideal R) : Set R) (S' : Set R) := by
    rw [Set.disjoint_left]
    intro r hr hrS
    obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hrS
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hr
    have h1 : (w : K') * (g / y ⟨(), t⟩ ^ e) = (s : K') := congrArg Subtype.val hw
    apply hcon s hs
    rw [← h1, show (w : K') * (g / y ⟨(), t⟩ ^ e) * (y ⟨(), t⟩ ^ e / g) = (w : K') by field_simp]
    exact w.2
  obtain ⟨q, hq, hzq, hqS⟩ := Ideal.exists_le_prime_disjoint _ S' hdisj
  obtain ⟨W, hRW, hunit, hlt⟩ := ClosedPointUnitSection.exists_valuationSubring R q
  have hBW : ∀ b : curveRing y, (b : K') ∈ W := fun b => hRW (Subring.inclusion hBR b)
  have hBunit : ∀ b : curveRing y, b ∉ m → W.valuation (b : K') = 1 := by
    intro b hb
    apply hunit (Subring.inclusion hBR b)
    intro hbq
    exact Set.disjoint_left.mp hqS hbq (Submonoid.mem_map.mpr ⟨b, hb, rfl⟩)
  have h1 := hW W hBW hBunit t
  have h2 : W.valuation (z : K') < 1 := hlt z (hzq (Ideal.subset_span (Set.mem_singleton z)))
  have h3 : (z : K') * (y ⟨(), t⟩ ^ e / g) = 1 := by
    show g / y ⟨(), t⟩ ^ e * (y ⟨(), t⟩ ^ e / g) = 1
    field_simp
  have h4 := congrArg W.valuation h3
  rw [map_mul, map_one] at h4
  have h5 : W.valuation (y ⟨(), t⟩ ^ e / g) ≤ 1 := (W.valuation_le_one_iff _).mpr h1
  have h6 : W.valuation (z : K') * W.valuation (y ⟨(), t⟩ ^ e / g) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right' h5) h2
  exact ne_of_lt h6 h4

theorem exists_mul_div_mem_curveRing {m : Ideal (curveRing y)} (hm : m.IsMaximal) {e : ℕ} {g : K'}
    (hg0 : g ≠ 0) (hgL : g ∈ chartLat y 1 e)
    (hW : ∀ W : ValuationSubring K', (∀ b : curveRing y, (b : K') ∈ W) →
      (∀ b : curveRing y, b ∉ m → W.valuation (b : K') = 1) → ∀ u : T, y ⟨(), u⟩ ^ e / g ∈ W)
    {h : K'} (hh : ∀ t : T, y ⟨(), t⟩ ≠ 0 → h / y ⟨(), t⟩ ^ e ∈ chartRingZ y (fun _ => t)) :
    ∃ s : curveRing y, s ∉ m ∧ (s : K') * (h / g) ∈ curveRing y := by
  classical
  have := hm.isPrime
  have key : ∀ t : T, ∃ s : curveRing y, s ∉ m ∧
      (y ⟨(), t⟩ ≠ 0 → (s : K') * (h / g) ∈ chartRingZ y (fun _ => t)) := by
    intro t
    by_cases ht : y ⟨(), t⟩ = 0
    · exact ⟨1, fun h1 => hm.ne_top ((Ideal.eq_top_iff_one _).mpr h1), fun h' => (h' ht).elim⟩
    · obtain ⟨s, hs, hsm⟩ := exists_mul_inv_mem y hg0 hgL hW t ht
      refine ⟨s, hs, fun _ => ?_⟩
      have e1 : (s : K') * (h / g) = h / y ⟨(), t⟩ ^ e * ((s : K') * (y ⟨(), t⟩ ^ e / g)) := by
        field_simp
      rw [e1]
      exact mul_mem (hh t ht) hsm
  choose S hSm hS using key
  refine ⟨∏ t, S t, fun hmem => ?_, ?_⟩
  · obtain ⟨t, -, ht⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hSm t ht
  · apply mem_curveRing_of_forall
    intro t ht
    have e1 : ((∏ u, S u : curveRing y) : K') * (h / g) =
        (∏ u ∈ Finset.univ.erase t, (S u : K')) * ((S t : K') * (h / g)) := by
      push_cast
      rw [← Finset.mul_prod_erase Finset.univ (fun u => (S u : K')) (Finset.mem_univ t)]
      ring
    rw [e1]
    exact mul_mem (prod_mem fun u _ => mem_chart_of_mem_curveRing y (S u).2 t ht) (hS t ht)

end ClosedPointAffineChart

theorem ClosedPointChart.proof (hU : ClosedPointUnitSection.Statement) : ClosedPointChart.Statement := by
  intro T _ K' _ _ y hy m hm
  obtain ⟨e, g, he, hg0, hgL, hW⟩ := hU T K' y hy m hm
  have := hm.isPrime
  obtain ⟨W, hBW, hBunit, hBlt⟩ := ClosedPointUnitSection.exists_valuationSubring (curveRing y) m
  obtain ⟨t0, ht0⟩ := CurveAffineCharts.exists_chart y hy
  obtain ⟨t, -, ht⟩ := Finset.exists_max_image Finset.univ (fun u => W.valuation (y ⟨(), u⟩))
    ⟨t0, Finset.mem_univ _⟩
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    have h1 := ht t0 (Finset.mem_univ _)
    rw [h0, map_zero] at h1
    exact ht0 ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))
  have hratio : ∀ u, y ⟨(), u⟩ / y ⟨(), t⟩ ∈ W := by
    intro u
    apply W.mem_of_valuation_le_one
    rw [map_div₀]
    exact (div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hyt))).mpr
      (ht u (Finset.mem_univ _))
  have hchartW : ∀ x ∈ chartRingZ y (fun _ => t), x ∈ W := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨⟨⟨⟩, u⟩, rfl⟩ := hx
      exact hratio u
    | algebraMap r => rw [eq_intCast]; exact intCast_mem W r
    | add x z _ _ hx hz => exact add_mem hx hz
    | mul x z _ _ hx hz => exact mul_mem hx hz
  have hinv : y ⟨(), t⟩ ^ e / g ∈ W := hW W hBW hBunit t
  have hgt : g / y ⟨(), t⟩ ^ e ∈ W :=
    hchartW _ (ClosedPointAffineChart.div_pow_mem_of_mem_chartLat y hgL t hyt)
  have hval : W.valuation (y ⟨(), t⟩ ^ e / g) = 1 := by
    have h1 : W.valuation (y ⟨(), t⟩ ^ e / g) * W.valuation (g / y ⟨(), t⟩ ^ e) = 1 := by
      rw [← map_mul, show y ⟨(), t⟩ ^ e / g * (g / y ⟨(), t⟩ ^ e) = 1 by
        field_simp [pow_ne_zero e hyt]]
      exact map_one _
    have h2 := (W.valuation_le_one_iff _).mpr hinv
    have h3 := (W.valuation_le_one_iff _).mpr hgt
    by_contra hne
    have h4 : W.valuation (y ⟨(), t⟩ ^ e / g) * W.valuation (g / y ⟨(), t⟩ ^ e) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h3) (lt_of_le_of_ne h2 hne)
    exact ne_of_lt h4 h1
  have hmon : ∀ u t' : T, y ⟨(), t'⟩ ≠ 0 →
      y ⟨(), u⟩ * y ⟨(), t⟩ ^ (e - 1) / y ⟨(), t'⟩ ^ e ∈ chartRingZ y (fun _ => t') := by
    intro u t' ht'
    have e1 : y ⟨(), u⟩ * y ⟨(), t⟩ ^ (e - 1) / y ⟨(), t'⟩ ^ e =
        (y ⟨(), u⟩ / y ⟨(), t'⟩) * (y ⟨(), t⟩ / y ⟨(), t'⟩) ^ (e - 1) := by
      rw [div_pow, div_mul_div_comm, mul_pow_sub_one (by omega : e ≠ 0)]
    rw [e1]
    exact mul_mem (ClosedPointAffineChart.ratio_mem y t' u)
      (pow_mem (ClosedPointAffineChart.ratio_mem y t' t) _)
  have hpow : y ⟨(), t⟩ * y ⟨(), t⟩ ^ (e - 1) = y ⟨(), t⟩ ^ e := mul_pow_sub_one (by omega) _
  obtain ⟨s0, hs0, hs0B⟩ :=
    ClosedPointAffineChart.exists_mul_div_mem_curveRing y hm hg0 hgL hW (hmon t)
  have ha0 : (⟨_, hs0B⟩ : curveRing y) ∉ m := by
    intro hmem
    have h1 := hBlt _ hmem
    change W.valuation ((s0 : K') * (y ⟨(), t⟩ * y ⟨(), t⟩ ^ (e - 1) / g)) < 1 at h1
    rw [map_mul, hpow, hval, hBunit s0 hs0, one_mul] at h1
    exact lt_irrefl _ h1
  refine ⟨t, hyt, fun u => ?_⟩
  obtain ⟨su, hsu, hsuB⟩ :=
    ClosedPointAffineChart.exists_mul_div_mem_curveRing y hm hg0 hgL hW (hmon u)
  refine ⟨⟨_, hsuB⟩ * s0, su * ⟨_, hs0B⟩, fun hmem => ?_, ?_⟩
  · rcases hm.isPrime.mem_or_mem hmem with h | h
    · exact hsu h
    · exact ha0 h
  · push_cast
    field_simp

end

end GroundTheory.Heights₂.Heights
