import Formalism.SharpRestriction.GrowthBounds.RootWeights.DegreeZeroWeightsBounded

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem casimirConjugation_apply (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) (X : Module.End K V) :
    casimirConjugation E c s X = ∑ i ∈ s, E c i * X * E i c := by
  unfold casimirConjugation
  simp [mul_assoc]

theorem casimirPowerW_zero (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) : casimirPower E c s 0 = 1 := by
  first
  | rfl
  | simp [casimirPower]
  | unfold casimirPower
    done

theorem casimirPowerW_succ (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) (q : ℕ) :
    casimirPower E c s (q + 1) = ∑ i ∈ s, E c i * casimirPower E c s q * E i c := by
  first
  | rw [casimirPower, casimirPower, pow_succ', Module.End.mul_apply, casimirConjugation_apply]
  | unfold casimirPower
    done

theorem casimirPowerW_succ_apply (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) (q : ℕ) (y : V) :
    casimirPower E c s (q + 1) y = ∑ i ∈ s, E c i (casimirPower E c s q (E i c y)) := by
  rw [casimirPowerW_succ]
  simp [LinearMap.sum_apply, Module.End.mul_apply]

theorem commutator_triple_product_leibniz {R : Type*} [Ring R] (A F W G : R) :
    A * (F * W * G) - (F * W * G) * A =
      (A * F - F * A) * W * G + F * (A * W - W * A) * G + F * W * (A * G - G * A) := by
  noncomm_ring

theorem casimirPowerW_comm_lower_block {E : GLOps n K V} (hE : IsGLRep E) (c a b : Fin n) (ha : a < c) (hb : b < c) (q : ℕ) :
    E a b * casimirPower E c (Iio c) q = casimirPower E c (Iio c) q * E a b := by
  induction q with
  | zero => rw [casimirPowerW_zero, one_mul, mul_one]
  | succ q ih =>
    rw [casimirPowerW_succ, ← sub_eq_zero, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    have hbc : b ≠ c := ne_of_lt hb
    have hca : c ≠ a := ne_of_gt ha
    have hA : ∀ i, E a b * E c i - E c i * E a b = -(if i = a then E c b else 0) := by
      intro i
      rw [hE.1 a b c i, if_neg hbc, zero_sub]
    have hG : ∀ i, E a b * E i c - E i c * E a b = (if b = i then E a c else 0) := by
      intro i
      rw [hE.1 a b i c, if_neg hca, sub_zero]
    have hW : E a b * casimirPower E c (Iio c) q - casimirPower E c (Iio c) q * E a b = 0 := by
      rw [ih, sub_self]
    simp_rw [commutator_triple_product_leibniz, hA, hG, hW, mul_zero, zero_mul, add_zero]
    rw [Finset.sum_add_distrib]
    simp [Finset.mem_Iio, ha, hb, neg_mul, ite_mul, mul_ite]

theorem casimirPowerW_comm_diagonal {E : GLOps n K V} (hE : IsGLRep E) (c : Fin n) (q : ℕ) :
    E c c * casimirPower E c (Iio c) q = casimirPower E c (Iio c) q * E c c := by
  induction q with
  | zero => rw [casimirPowerW_zero, one_mul, mul_one]
  | succ q ih =>
    rw [casimirPowerW_succ, ← sub_eq_zero, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro i hi
    have hic : i ≠ c := ne_of_lt (Finset.mem_Iio.mp hi)
    have hW : E c c * casimirPower E c (Iio c) q - casimirPower E c (Iio c) q * E c c = 0 := by
      rw [ih, sub_self]
    rw [commutator_triple_product_leibniz, hW, hE.1 c c c i, hE.1 c c i c]
    simp [hic, Ne.symm hic]

theorem casimirPowerW_preserves_weight {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) (c : Fin n) (s : Finset (Fin n)) (q : ℕ) :
    ∀ (ν : Fin n → ℤ) (y : V), y ∈ weightSp E ν → casimirPower E c s q y ∈ weightSp E ν := by
  induction q with
  | zero =>
    intro ν y hy
    simpa [casimirPowerW_zero] using hy
  | succ q ih =>
    intro ν y hy
    rw [casimirPowerW_succ_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h3 := hs c i _ _ (ih _ _ (hs i c ν y hy))
    have e : ν + rootW i c + rootW c i = ν := by
      funext k
      simp only [rootW, Pi.add_apply, Pi.sub_apply]
      abel
    rwa [e] at h3

def ProjectorRecursionProperty (E : GLOps n K V) (c : Fin n) (s : ℕ) (y : V) : Prop :=
  E c c y = -(s : K) • y ∧
    ∀ j, j < c → ∑ i ∈ Iio c, E j i (E i c y) = ((s : K) + (c.val : K)) • E j c y

theorem gl_commutation_relation_apply {E : GLOps n K V} (hE : IsGLRep E) (a b c d : Fin n) (y : V) :
    E a b (E c d y) = E c d (E a b y) + (if b = c then E a d y else 0) - (if d = a then E c b y else 0) := by
  have h := LinearMap.congr_fun (hE.1 a b c d) y
  have e1 : ((if b = c then E a d else 0) : Module.End K V) y = if b = c then E a d y else 0 := by
    split_ifs <;> rfl
  have e2 : ((if d = a then E c b else 0) : Module.End K V) y = if d = a then E c b y else 0 := by
    split_ifs <;> rfl
  simp only [LinearMap.sub_apply, Module.End.mul_apply, e1, e2] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

theorem projector_recursion_base {E : GLOps n K V} (hE : IsGLRep E) (c : Fin n) (u : V) (hu0 : u ∈ weightSp E 0)
    (hu : ∀ a b : Fin n, a < c → b < c → E a b u = 0) : ProjectorRecursionProperty E c 0 u := by
  refine ⟨?_, ?_⟩
  · have h := hu0
    unfold weightSp at h
    have h2 := (Submodule.mem_iInf _).mp h c
    rw [LinearMap.mem_ker] at h2
    simpa [sub_eq_zero] using h2
  · intro j hj
    have h : ∀ i ∈ Iio c, E j i (E i c u) = E j c u := by
      intro i hi
      rw [gl_commutation_relation_apply hE j i i c u, hu j i hj (Finset.mem_Iio.mp hi), map_zero, if_pos rfl,
        if_neg (ne_of_gt hj), zero_add, sub_zero]
    rw [Finset.sum_congr rfl h, Finset.sum_const, Fin.card_Iio, Nat.cast_zero, zero_add,
      Nat.cast_smul_eq_nsmul]

theorem raising_to_column_commute {E : GLOps n K V} (hE : IsGLRep E) (c i j : Fin n) (hi : i < c) (hj : j < c) (y : V) :
    E i c (E j c y) = E j c (E i c y) := by
  rw [gl_commutation_relation_apply hE i c j c y, if_neg (ne_of_gt hj), if_neg (ne_of_gt hi), add_zero, sub_zero]

theorem projector_recursion_lower {E : GLOps n K V} (hE : IsGLRep E) (c l : Fin n) (hl : l < c) (s : ℕ) (y : V)
    (hy : ProjectorRecursionProperty E c s y) : ProjectorRecursionProperty E c (s + 1) (E l c y) := by
  obtain ⟨h1, h2⟩ := hy
  have hlc : l ≠ c := ne_of_lt hl
  refine ⟨?_, ?_⟩
  · rw [gl_commutation_relation_apply hE c c l c y, if_neg (Ne.symm hlc), if_pos rfl, h1, map_smul, add_zero]
    push_cast
    rw [neg_add, add_smul, neg_smul, neg_smul, one_smul]
    abel
  · intro j hj
    have hcj : c ≠ j := ne_of_gt hj
    have key : ∀ i ∈ Iio c, E j i (E i c (E l c y)) =
        E l c (E j i (E i c y)) + (if i = l then E j c (E i c y) else 0) := by
      intro i hi
      rw [raising_to_column_commute hE c i l (Finset.mem_Iio.mp hi) hl y, gl_commutation_relation_apply hE j i l c (E i c y),
        if_neg hcj, sub_zero]
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← map_sum, h2 j hj, map_smul,
      Finset.sum_ite_eq', if_pos (Finset.mem_Iio.mpr hl), raising_to_column_commute hE c l j hl hj y]
    push_cast
    simp only [add_smul, one_smul]
    abel

theorem casimirPowerW_comm_lower_apply {E : GLOps n K V} (hE : IsGLRep E) (c a b : Fin n) (ha : a < c) (hb : b < c) (q : ℕ)
    (y : V) : E a b (casimirPower E c (Iio c) q y) = casimirPower E c (Iio c) q (E a b y) := by
  rw [← Module.End.mul_apply, casimirPowerW_comm_lower_block hE c a b ha hb q, Module.End.mul_apply]

theorem casimirPowerW_comm_diagonal_apply {E : GLOps n K V} (hE : IsGLRep E) (c : Fin n) (q : ℕ) (y : V) :
    E c c (casimirPower E c (Iio c) q y) = casimirPower E c (Iio c) q (E c c y) := by
  rw [← Module.End.mul_apply, casimirPowerW_comm_diagonal hE c q, Module.End.mul_apply]

theorem raising_casimirPower_commutator {E : GLOps n K V} (hE : IsGLRep E) (c j : Fin n) (hj : j < c) (q : ℕ) :
    ∀ (s : ℕ) (y : V), ProjectorRecursionProperty E c s y →
      E j c (casimirPower E c (Iio c) q y) = casimirPower E c (Iio c) q (E j c y) +
        ((q : K) * (2 * (s : K) + (c.val : K) + (q : K))) • casimirPower E c (Iio c) (q - 1) (E j c y) := by
  induction q with
  | zero =>
    intro s y _
    simp [casimirPowerW_zero]
  | succ q ih =>
    intro s y hy
    have hPj : ProjectorRecursionProperty E c (s + 1) (E j c y) := projector_recursion_lower hE c j hj s y hy
    have hterm : ∀ i ∈ Iio c, E j c (E c i (casimirPower E c (Iio c) q (E i c y))) =
        E c i (casimirPower E c (Iio c) q (E i c (E j c y))) +
        ((q : K) * (2 * ((s + 1 : ℕ) : K) + (c.val : K) + (q : K))) •
          E c i (casimirPower E c (Iio c) (q - 1) (E i c (E j c y))) +
        casimirPower E c (Iio c) q (E j i (E i c y)) -
        (if i = j then casimirPower E c (Iio c) q (E c c (E j c y)) else 0) := by
      intro i hi
      have hi' : i < c := Finset.mem_Iio.mp hi
      rw [gl_commutation_relation_apply hE j c c i, if_pos rfl, ih (s + 1) (E i c y) (projector_recursion_lower hE c i hi' s y hy),
        ← raising_to_column_commute hE c i j hi' hj y, map_add, map_smul, casimirPowerW_comm_lower_apply hE c j i hj hi' q]
      split_ifs with h
      · subst h
        rw [casimirPowerW_comm_diagonal_apply hE c q]
      · rfl
    have hW : ((q : K) * (2 * ((s + 1 : ℕ) : K) + (c.val : K) + (q : K))) •
        ∑ i ∈ Iio c, E c i (casimirPower E c (Iio c) (q - 1) (E i c (E j c y))) =
        ((q : K) * (2 * ((s + 1 : ℕ) : K) + (c.val : K) + (q : K))) • casimirPower E c (Iio c) q (E j c y) := by
      rcases q with _ | q'
      · simp
      · rw [Nat.add_sub_cancel, ← casimirPowerW_succ_apply]
    have key : (q : K) * (2 * ((s + 1 : ℕ) : K) + (c.val : K) + (q : K)) + ((s : K) + (c.val : K)) -
        -((s + 1 : ℕ) : K) = ((q + 1 : ℕ) : K) * (2 * (s : K) + (c.val : K) + ((q + 1 : ℕ) : K)) := by
      push_cast
      ring
    rw [casimirPowerW_succ_apply E c (Iio c) q y, map_sum (E j c), Finset.sum_congr rfl hterm,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, hW,
      ← map_sum (casimirPower E c (Iio c) q), hy.2 j hj, map_smul (casimirPower E c (Iio c) q), Finset.sum_ite_eq',
      if_pos (Finset.mem_Iio.mpr hj), hPj.1, map_smul (casimirPower E c (Iio c) q),
      ← casimirPowerW_succ_apply E c (Iio c) q (E j c y), Nat.add_sub_cancel, ← key]
    simp only [add_smul, sub_smul]
    abel

theorem rootWeight_entries_sum_zero (a b : Fin n) : ∑ x, rootW a b x = 0 := by
  simp [rootW, Finset.sum_sub_distrib]

theorem casimirPowerW_vanishes_large {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) (c : Fin n) (L : ℕ) (hL : DegreeZeroWeightsBounded E L) (q : ℕ) :
    ∀ (s : ℕ) (ν : Fin n → ℤ) (z : V), z ∈ weightSp E ν → (∑ a, ν a = 0) → ν c = -(s : ℤ) → L < q + s →
      casimirPower E c (Iio c) q z = 0 := by
  induction q with
  | zero =>
    intro s ν z hz hsum hc hLq
    have hbot : weightSp E ν = ⊥ := by
      by_contra hne
      have h := hL ν hsum hne c
      rw [hc, abs_neg, Nat.abs_cast] at h
      omega
    rw [hbot, Submodule.mem_bot] at hz
    rw [hz, map_zero]
  | succ q ih =>
    intro s ν z hz hsum hc hLq
    rw [casimirPowerW_succ_apply]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hic : i ≠ c := ne_of_lt (Finset.mem_Iio.mp hi)
    have h1 := hs i c ν z hz
    have hsum' : ∑ a, (ν + rootW i c) a = 0 := by
      simp only [Pi.add_apply, Finset.sum_add_distrib, hsum, rootWeight_entries_sum_zero, add_zero]
    have hc' : (ν + rootW i c) c = -((s + 1 : ℕ) : ℤ) := by
      rw [Pi.add_apply, rootW, Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm hic), Pi.single_eq_same, hc]
      push_cast
      ring
    rw [ih (s + 1) _ _ h1 hsum' hc' (by omega), map_zero]

def extremalProjectorCoeff (K : Type*) [Field K] (m q : ℕ) : K :=
  (-1 : K) ^ q * ((m.factorial : K) / (((q + m).factorial : K) * (q.factorial : K)))

theorem extremalProjector_apply (E : GLOps n K V) (c : Fin n) (L : ℕ) (u : V) :
    extremalProjector E c L u = ∑ q ∈ range (L + 1), extremalProjectorCoeff K c.val q • casimirPower E c (Iio c) q u := by
  unfold extremalProjector casimirPowerScaled
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_smul]
  rfl

theorem extremalProjectorCoeff_zero [CharZero K] (m : ℕ) : extremalProjectorCoeff K m 0 = 1 := by
  have h : (m.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  simp [extremalProjectorCoeff, h]

theorem extremalProjectorCoeff_succ [CharZero K] (m q : ℕ) :
    extremalProjectorCoeff K m (q + 1) * (((q + 1 : ℕ) : K) * (2 * ((0 : ℕ) : K) + (m : K) + ((q + 1 : ℕ) : K))) = - extremalProjectorCoeff K m q := by
  unfold extremalProjectorCoeff
  rw [show q + 1 + m = (q + m) + 1 by omega, Nat.factorial_succ (q + m), Nat.factorial_succ q]
  have h3 : ((q + m).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h4 : (q.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h5 : ((q + m + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h6 : ((q + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast at h5 h6 ⊢
  field_simp
  ring

theorem extremal_projector_properties [CharZero K] {E : GLOps n K V} (hE : IsGLRep E) (c : Fin n) (L : ℕ) (hL : DegreeZeroWeightsBounded E L) (u : V)
    (hu0 : u ∈ weightSp E 0) (hu : ∀ a b : Fin n, a < c → b < c → E a b u = 0) :
    (∀ j, j < c → E j c (extremalProjector E c L u) = 0) ∧
    (∀ a b : Fin n, a < c → b < c → E a b (extremalProjector E c L u) = 0) ∧
    extremalProjector E c L u ∈ weightSp E 0 ∧
    ∃ w : Fin n → V, extremalProjector E c L u = u + ∑ i ∈ Finset.Iio c, E c i (w i) := by
  have hs := gl_rep_shifts_weights hE
  have hPP := projector_recursion_base hE c u hu0 hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    have hjc : j ≠ c := ne_of_lt hj
    have htop : casimirPower E c (Iio c) L (E j c u) = 0 := by
      refine casimirPowerW_vanishes_large hs c L hL L 1 (0 + rootW j c) (E j c u) (hs j c 0 u hu0) ?_ ?_ (by omega)
      · simp only [zero_add, rootWeight_entries_sum_zero]
      · simp [rootW, hjc]
    rw [extremalProjector_apply, map_sum]
    have h1 : ∀ q ∈ range (L + 1), E j c (extremalProjectorCoeff K c.val q • casimirPower E c (Iio c) q u) =
        extremalProjectorCoeff K c.val q • casimirPower E c (Iio c) q (E j c u) +
          (extremalProjectorCoeff K c.val q * ((q : K) * (2 * ((0 : ℕ) : K) + (c.val : K) + (q : K)))) •
            casimirPower E c (Iio c) (q - 1) (E j c u) := by
      intro q _
      rw [map_smul, raising_casimirPower_commutator hE c j hj q 0 u hPP, smul_add, smul_smul]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_range_succ, htop, smul_zero, add_zero,
      Finset.sum_range_succ']
    have h2 : ∀ q ∈ range L, (extremalProjectorCoeff K c.val (q + 1) *
        (((q + 1 : ℕ) : K) * (2 * ((0 : ℕ) : K) + (c.val : K) + ((q + 1 : ℕ) : K)))) •
          casimirPower E c (Iio c) (q + 1 - 1) (E j c u) = - (extremalProjectorCoeff K c.val q • casimirPower E c (Iio c) q (E j c u)) := by
      intro q _
      rw [extremalProjectorCoeff_succ, Nat.add_sub_cancel, neg_smul]
    rw [Finset.sum_congr rfl h2, Finset.sum_neg_distrib]
    simp
  · intro a b ha hb
    rw [extremalProjector_apply, map_sum]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [map_smul, casimirPowerW_comm_lower_apply hE c a b ha hb, hu a b ha hb, map_zero, smul_zero]
  · rw [extremalProjector_apply]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (casimirPowerW_preserves_weight hs c _ q 0 u hu0)
  · refine ⟨fun i => ∑ q ∈ range L, extremalProjectorCoeff K c.val (q + 1) • casimirPower E c (Iio c) q (E i c u), ?_⟩
    rw [extremalProjector_apply, Finset.sum_range_succ', extremalProjectorCoeff_zero, casimirPowerW_zero, one_smul, Module.End.one_apply, add_comm]
    congr 1
    simp only [map_sum, map_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [casimirPowerW_succ_apply, Finset.smul_sum]

end Formalism.MainNotions.G.GLWeightTheory
