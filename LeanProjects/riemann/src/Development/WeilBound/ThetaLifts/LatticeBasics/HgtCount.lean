import Mathlib

noncomputable section

namespace GlobalTheory.ThK.Dbl.Hgt

open scoped NNReal ENNReal
open MeasureTheory Topology

theorem exists_cover {A : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A] (ν : Measure A) [ν.IsAddLeftInvariant]
    {X V Z : Set A} (hV : MeasurableSet V) (h0 : ν V ≠ 0) (hZ : ν Z ≠ ⊤) (hXZ : ∀ x ∈ X, ∀ v ∈ V, x + v ∈ Z) :
    ∃ s : Finset A, s.card * ν V ≤ ν Z ∧ ∀ x ∈ X, ∃ y ∈ s, ∃ v ∈ V, ∃ v' ∈ V, x - y = v - v' := by
  classical
  by_contra! h
  let T : A → Set A := fun x => (fun a => -x + a) ⁻¹' V
  have bd : ∀ s : Finset A, (s : Set A) ⊆ X → (s : Set A).PairwiseDisjoint T → s.card * ν V ≤ ν Z := fun s h1 h2 => by
    have := measure_biUnion_finset (μ := ν) h2 fun b _ => measurable_const_add _ hV
    simp only [T, measure_preimage_add, Finset.sum_const, nsmul_eq_mul] at this
    rw [← this]
    exact measure_mono (Set.iUnion₂_subset fun x hx a ha => by simpa using hXZ x (h1 hx) _ ha)
  obtain ⟨v₀, hv₀⟩ := nonempty_of_measure_ne_zero h0
  have key : ∀ k : ℕ, ∃ s : Finset A, s.card = k ∧ (s : Set A) ⊆ X ∧ (s : Set A).PairwiseDisjoint T := fun k => by
    induction k with
    | zero => exact ⟨∅, rfl, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨s, rfl, h1, h2⟩ := ih
      obtain ⟨x, hx, hx'⟩ := h s (bd s h1 h2)
      refine ⟨insert x s, Finset.card_insert_of_notMem fun hs => hx' x hs v₀ hv₀ v₀ hv₀ (by simp), ?_, ?_⟩
      · rw [Finset.coe_insert]; exact Set.insert_subset hx h1
      · rw [Finset.coe_insert]
        exact h2.insert fun y hy _ => Set.disjoint_left.2 fun a ha hb => hx' y hy (-y + a) hb (-x + a) ha (by rw [add_sub_add_right_eq_sub, neg_sub_neg])
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt h0 hZ
  obtain ⟨s, rfl, h1, h2⟩ := key N
  exact hN.not_ge (bd s h1 h2)

theorem integrable_of_count {G : Type} [MeasurableSpace G] (μ : Measure G) {f : G → ℝ} (hf : Measurable f) (h0 : ∀ g, 0 < f g)
    {R : ℝ} (h1 : 1 ≤ R) (hR : ∀ g, f g ≤ R) {C : ℝ≥0∞} (hC : C ≠ ⊤) (b : ℝ≥0)
    (h : ∀ j : ℕ, μ {g | (1 / 2) ^ j ≤ f g} ≤ C * b ^ j) : ∃ t₀ : ℝ, ∀ t, t₀ ≤ t → Integrable (fun g => f g ^ t) μ := by
  classical
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (b + 1) by positivity) (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨k, fun t ht => ⟨(hf.pow_const t).aestronglyMeasurable, ?_⟩⟩
  have t0 : 0 ≤ t := (Nat.cast_nonneg k).trans ht
  let P : ℕ → Set G := fun j => {g | (1 / 2) ^ j ≤ f g ∧ f g ≤ 2 * R * (1 / 2) ^ j}
  have hP : ⋃ j, P j = Set.univ := Set.eq_univ_of_forall fun g => by
    have ex : ∃ j : ℕ, (1 / 2 : ℝ) ^ j ≤ f g := (exists_pow_lt_of_lt_one (h0 g) (by norm_num)).imp fun _ => le_of_lt
    refine Set.mem_iUnion.2 ⟨Nat.find ex, Nat.find_spec ex, ?_⟩
    rcases e : Nat.find ex with _ | j
    · have := hR g; simp; linarith
    · have := Nat.find_min ex (m := j) (by omega)
      have p : (0 : ℝ) < (1 / 2) ^ j := by positivity
      rw [pow_succ]; nlinarith
  set ρ : ℝ≥0∞ := ENNReal.ofReal ((1 / 2) ^ t) * b
  have hρ : ρ < 1 := by
    have : ((1 / 2 : ℝ)) ^ t ≤ (1 / 2) ^ k := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) ht
    rw [lt_div_iff₀ (by positivity)] at hk
    have p : (0 : ℝ) < (1 / 2) ^ t := by positivity
    rw [show ρ = ENNReal.ofReal ((1 / 2) ^ t * b) by rw [ENNReal.ofReal_mul p.le, ENNReal.ofReal_coe_nnreal], ENNReal.ofReal_lt_one]
    nlinarith [b.2, show (0 : ℝ) ≤ b from b.2]
  calc ∫⁻ g, ‖f g ^ t‖ₑ ∂μ = ∫⁻ g in ⋃ j, P j, ‖f g ^ t‖ₑ ∂μ := by rw [hP, Measure.restrict_univ]
    _ ≤ ∑' j, ∫⁻ g in P j, ‖f g ^ t‖ₑ ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' j, ENNReal.ofReal ((2 * R) ^ t) * C * ρ ^ j := ENNReal.tsum_le_tsum fun j => by
      refine (setLIntegral_mono (g := fun _ => ENNReal.ofReal ((2 * R) ^ t) * ENNReal.ofReal ((1 / 2) ^ t) ^ j)
        measurable_const fun g hg => ?_).trans ?_
      · rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (h0 g).le _), ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_mul_natCast (by norm_num), mul_comm t, Real.rpow_natCast_mul (by norm_num),
          ← Real.mul_rpow (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (h0 g).le hg.2 t0)
      · rw [setLIntegral_const]
        refine (mul_le_mul_right ((measure_mono fun g hg => hg.1).trans (h j)) _).trans_eq ?_
        simp only [ρ, mul_pow]; ring
    _ < ⊤ := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.lt_top)
        (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hρ))

theorem count_grp {R B κ : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Ring B] [Algebra R B] [TopologicalSpace B]
    [IsTopologicalRing B] [T2Space B] [Fintype κ] (c : B ≃ₗ[R] (κ → R)) (hc : Continuous c) (hc' : Continuous c.symm)
    (H : Subgroup Bˣ) (hH : IsClosed (H : Set Bˣ)) {Ω : Set B} (hΩ : IsCompact Ω) {W : Set R} (hW : IsCompact W) :
    ∃ (X : Set R) (U : Set H), IsCompact X ∧ IsCompact U ∧ ∀ (l : Rˣ) (s : Finset R),
      (∀ x ∈ X, ∃ y ∈ s, ∃ w ∈ W, x - y = l * l * w) → ∀ [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant],
        μ {g | l.1 • g.1.1 ∈ Ω ∧ l.1 • (g⁻¹).1.1 ∈ Ω} ≤ (s.card : ℝ≥0∞) ^ Fintype.card κ * μ U := by
  classical
  let W' : Set ((κ → R) × (κ → R)) := (Set.univ.pi fun _ => W) ×ˢ Set.univ.pi fun _ => W
  let Ω' : Set B := (fun y : B × (κ → R) × (κ → R) => 1 + y.1 * c.symm (y.2.1 - y.2.2)) '' Ω ×ˢ W'
  have hΩ' : IsCompact Ω' := (hΩ.prod ((isCompact_univ_pi fun _ => hW).prod (isCompact_univ_pi fun _ => hW))).image (by fun_prop)
  have em : IsClosedEmbedding (fun k : H => Units.embedProduct B k.1) :=
    Units.isClosedEmbedding_embedProduct.comp hH.isClosedEmbedding_subtypeVal
  refine ⟨⋃ k, (fun y => c y k) '' Ω, _, isCompact_iUnion fun k => hΩ.image (by fun_prop),
    em.isCompact_preimage (hΩ'.prod (hΩ'.image MulOpposite.continuous_op)), fun l s hs _ _ μ _ => ?_⟩
  let S : (κ → R) → Set H := fun y => {g | l.1 • (g⁻¹).1.1 ∈ Ω ∧ ∀ k, ∃ w ∈ W, c (l.1 • g.1.1) k - y k = l * l * w}
  have key : ∀ y, ∀ g ∈ S y, ∀ g' ∈ S y, (g⁻¹ * g').1.1 ∈ Ω' := fun y g hg g' hg' => by
    choose w hw e using hg.2
    choose w' hw' e' using hg'.2
    refine ⟨(_, w', w), ⟨hg.1, fun k _ => hw' k, fun k _ => hw k⟩, ?_⟩
    have e1 : g'.1.1 - g.1.1 = l.1 • c.symm (w' - w) := by
      refine c.injective (funext fun k => l.isUnit.mul_left_cancel ?_)
      have := e k
      have := e' k
      simp only [map_smul, map_sub, LinearEquiv.apply_symm_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at *
      linear_combination e' k - e k
    change 1 + l.1 • (g.1⁻¹).1 * c.symm (w' - w) = (g.1⁻¹).1 * g'.1.1
    rw [smul_mul_assoc, ← mul_smul_comm, ← e1, mul_sub, Units.inv_mul, add_sub_cancel]
  refine (measure_mono (t := ⋃ y ∈ Fintype.piFinset fun _ : κ => s, S y) fun g hg => ?_).trans
    ((measure_biUnion_finset_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (μ ((fun k : H => Units.embedProduct B k.1) ⁻¹'
      Ω' ×ˢ (MulOpposite.op '' Ω'))) fun y _ => ?_).trans_eq (by simp)))
  · choose y hy hy' using fun k => hs _ (Set.mem_iUnion.2 ⟨k, _, hg.1, rfl⟩)
    exact Set.mem_iUnion₂.2 ⟨y, Fintype.mem_piFinset.2 hy, hg.2, hy'⟩
  · rcases (S y).eq_empty_or_nonempty with e | ⟨g, hg⟩
    · simp [e]
    · refine (measure_mono ?_).trans_eq (measure_preimage_mul μ g⁻¹ _)
      exact fun g' hg' => ⟨key y g hg g' hg', _, key y g' hg' g hg, by simp⟩

end GlobalTheory.ThK.Dbl.Hgt

end
