import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.Bridge

def fixedField {E : Type} [Field E] (c : E ≃+* E) : Subfield E :=
  RingHom.eqLocusField (c : E →+* E) (RingHom.id E)

theorem mem_fixedField {E : Type} [Field E] (c : E ≃+* E) (x : E) : x ∈ fixedField c ↔ c x = x := Iff.rfl

theorem finrank_fixedField {E : Type} [Field E] [CharZero E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x)
    (hne : ∃ y, c y ≠ y) : Module.finrank (fixedField c) E = 2 := by
  obtain ⟨y, hy⟩ := hne
  set d := y - c y with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 hy.symm
  have hcd : c d = -d := by rw [hd, map_sub, hc]; ring
  let f : (fixedField c × fixedField c) →ₗ[fixedField c] E :=
    { toFun := fun p => (p.1 : E) + (p.2 : E) * d
      map_add' := by intro p q; simp; ring
      map_smul' := by
        intro a p
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply, Subfield.coe_mul]
        change _ = (a : E) * _
        ring }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ h
    have h1 : (a : E) + (b : E) * d = 0 := h
    have h2 := congrArg c h1
    rw [map_add, map_mul, (mem_fixedField c _).1 a.2, (mem_fixedField c _).1 b.2, hcd, map_zero] at h2
    have ha : (a : E) = 0 := by linear_combination (h1 + h2) / 2
    have hb : (b : E) * d = 0 := by linear_combination (h1 - h2) / 2
    have hb' : (b : E) = 0 := (mul_eq_zero.1 hb).resolve_right hd0
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb')
  have hsurj : Function.Surjective f := by
    intro z
    refine ⟨(⟨(z + c z) / 2, ?_⟩, ⟨(z - c z) / (2 * d), ?_⟩), ?_⟩
    · rw [mem_fixedField, map_div₀, map_add, hc, map_ofNat, add_comm]
    · rw [mem_fixedField, map_div₀, map_sub, hc, map_mul, map_ofNat, hcd]
      field_simp
      ring
    · change (z + c z) / 2 + (z - c z) / (2 * d) * d = z
      field_simp
      ring
  rw [← (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq]
  simp

theorem unram_of_involution {E : Type} [nE : NontriviallyNormedField E] [CharZero E] [IsUltrametricDist E]
    [LocallyCompactSpace E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (hne : ∃ y, c y ≠ y)
    (hn : ∀ y, ‖c y‖ = ‖y‖) (hu : ∀ y : E, ∃ x, c x = x ∧ ‖y‖ = ‖x‖) :
    ∃ (F : Type) (_ : NontriviallyNormedField F) (_ : NormedAlgebra F E) (st : StarRing E),
      GlobalTheory.JR.Unram F E ∧ ∀ y, st.star y = c y := by
  letI nF : NontriviallyNormedField (fixedField c) :=
    { (inferInstance : NormedField (fixedField c)) with
      non_trivial := by
        obtain ⟨y, hy⟩ := NontriviallyNormedField.non_trivial (α := E)
        obtain ⟨x, hx, hxy⟩ := hu y
        exact ⟨⟨x, hx⟩, by change 1 < ‖x‖; rwa [← hxy]⟩ }
  letI nA : NormedAlgebra (fixedField c) E :=
    { (inferInstance : Algebra (fixedField c) E) with
      norm_smul_le := fun a y => norm_mul_le (a : E) y }
  letI st : StarRing E :=
    { star := c
      star_involutive := hc
      star_mul := fun a b => by rw [map_mul, mul_comm]
      star_add := fun a b => map_add c a b }
  have hcont : Continuous c := (AddMonoidHomClass.isometry_of_norm c hn).continuous
  have hcl : IsClosed (fixedField c : Set E) := isClosed_eq hcont continuous_id
  refine ⟨fixedField c, nF, nA, st, ?_, fun _ => rfl⟩
  exact
    { charZero := inferInstance
      ultraF := inferInstance
      ultraE := inferInstance
      lcF := hcl.locallyCompactSpace
      lcE := inferInstance
      finrank_eq := finrank_fixedField c hc hne
      star_fix := fun x => x.2
      star_ne := hne
      norm_star := hn
      unram := fun y => by
        obtain ⟨x, hx, hxy⟩ := hu y
        exact ⟨⟨x, hx⟩, hxy⟩ }

theorem locallyCompact_of_complete {O E : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [NormedField E] [Algebra O E] (hinj : Function.Injective (algebraMap O E))
    (hball : ∀ y : E, ‖y‖ ≤ 1 ↔ y ∈ (algebraMap O E).range) : LocallyCompactSpace E := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπ0 : algebraMap O E π ≠ 0 := fun h => hπ.ne_zero (hinj (by rw [h, map_zero]))
  have hpos : 0 < ‖algebraMap O E π‖ := norm_pos_iff.2 hπ0
  have hlt : ‖algebraMap O E π‖ < 1 := by
    by_contra h
    have : ‖(algebraMap O E π)⁻¹‖ ≤ 1 := by
      rw [norm_inv]; exact inv_le_one_of_one_le₀ (not_lt.1 h)
    obtain ⟨z, hz⟩ := (hball _).1 this
    apply hπ.not_isUnit
    refine IsUnit.of_mul_eq_one z (hinj ?_)
    rw [map_mul, hz, map_one, mul_inv_cancel₀ hπ0]
  have hmem : ∀ (n : ℕ) (x : O), x ∈ IsLocalRing.maximalIdeal O ^ n ↔
      ‖algebraMap O E x‖ ≤ ‖algebraMap O E π‖ ^ n := by
    intro n x
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, rfl⟩
      rw [map_mul, map_pow, norm_mul, norm_pow]
      exact mul_le_of_le_one_left (by positivity) ((hball _).2 ⟨a, rfl⟩)
    · intro h
      have : ‖algebraMap O E x / algebraMap O E π ^ n‖ ≤ 1 := by
        rw [norm_div, norm_pow]; exact div_le_one_of_le₀ h (by positivity)
      obtain ⟨z, hz⟩ := (hball _).1 this
      refine ⟨z, hinj ?_⟩
      rw [map_mul, map_pow, hz, div_mul_cancel₀ _ (pow_ne_zero _ hπ0)]
  letI : MetricSpace O := MetricSpace.induced (algebraMap O E) hinj inferInstance
  have hdist : ∀ a b : O, dist a b = ‖algebraMap O E (a - b)‖ := by
    intro a b
    rw [map_sub, ← dist_eq_norm]; rfl
  have hcomp : CompleteSpace O := by
    refine Metric.complete_of_convergent_controlled_sequences (fun N => ‖algebraMap O E π‖ ^ N)
      (fun n => by positivity) fun u hu => ?_
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := IsLocalRing.maximalIdeal O) (M := O) inferInstance (f := u) (by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hmem, ← hdist]
      exact (hu m m n le_rfl hmn).le)
    refine ⟨L, tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hlt))⟩
    have := hL n
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hmem, ← hdist] at this
  have htb : TotallyBounded (Set.univ : Set O) := by
    refine Metric.totallyBounded_iff.2 fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hlt
    haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) := ‹Finite (IsLocalRing.ResidueField O)›
    haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O ^ n) :=
      Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
    refine ⟨Set.range (Quotient.out : O ⧸ IsLocalRing.maximalIdeal O ^ n → O), Set.finite_range _, fun x _ => ?_⟩
    refine Set.mem_biUnion (Set.mem_range_self (Ideal.Quotient.mk _ x)) ?_
    rw [Metric.mem_ball, hdist]
    refine lt_of_le_of_lt ((hmem n _).1 ?_) hn
    rw [← Ideal.Quotient.eq]
    exact (Ideal.Quotient.mk_out _).symm
  have hcpt : IsCompact (Set.univ : Set O) := isCompact_iff_totallyBounded_isComplete.2 ⟨htb, complete_univ⟩
  have hcont : Continuous (algebraMap O E) := continuous_induced_dom
  refine (hcpt.image hcont).locallyCompactSpace_of_mem_nhds_of_addGroup (x := 0) ?_
  refine Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) fun y hy => ?_
  obtain ⟨z, hz⟩ := (hball y).1 (by simpa using hy)
  exact ⟨z, trivial, hz⟩

open WithZero in

theorem val_conj {E : Type} [Field E] (v : Valuation E (WithZero (Multiplicative ℤ))) (π : E)
    (hπ : v π = exp (-1)) (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (hle : ∀ y, v y ≤ 1 → v (c y) ≤ 1) (y : E) :
    v (c y) = v y := by
  have hle2 : ∀ a b : E, b ≠ 0 → v a ≤ v b → v (c a) ≤ v (c b) := by
    intro a b hb h
    have hb' : c b ≠ 0 := by simpa using hb
    have h1 := hle (a / b) (by rw [map_div₀]; exact div_le_one_of_le₀ h zero_le')
    rw [map_div₀, map_div₀, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff v).2 hb'))] at h1
    exact h1
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, map_zero] at hπ; exact exp_ne_zero hπ.symm
  have hcπ0 : c π ≠ 0 := by simpa using hπ0
  have h1 : v (c π) ≤ v π := by
    have : v (c π) < 1 := by
      by_contra h
      have := hle2 1 (c π) hcπ0 (by rw [map_one]; exact not_lt.1 h)
      rw [map_one, map_one, hc, hπ, ← exp_zero, exp_le_exp] at this
      omega
    rw [hπ]
    rw [← exp_log ((Valuation.ne_zero_iff v).2 hcπ0), ← exp_zero, exp_lt_exp] at this
    rw [← exp_log ((Valuation.ne_zero_iff v).2 hcπ0), exp_le_exp]
    omega
  have h2 : v (c π) = v π := by
    have := hle2 _ _ hπ0 h1
    rw [hc] at this
    exact le_antisymm h1 this
  by_cases hy : y = 0
  · simp [hy]
  have h3 : v y = v (π ^ (-log (v y))) := by
    rw [map_zpow₀, hπ, ← exp_zsmul]
    simp [exp_log ((Valuation.ne_zero_iff v).2 hy)]
  have h4 : v (c (π ^ (-log (v y)))) = v (π ^ (-log (v y))) := by
    rw [map_zpow₀, map_zpow₀, map_zpow₀, h2]
  refine le_antisymm ?_ ?_
  · exact (hle2 _ _ (zpow_ne_zero _ hπ0) h3.le).trans (h4.trans h3.symm).le
  · exact (h4.trans h3.symm).symm.le.trans (hle2 _ _ hy h3.ge)

open WithZero in

theorem exists_fixed_val {E : Type} [Field E] (v : Valuation E (WithZero (Multiplicative ℤ))) (π : E)
    (hπ : v π = exp (-1)) (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (hv : ∀ y, v (c y) = v y)
    (a : E) (ha : v a ≤ 1) (hd : v (a - c a) = 1) (y : E) : ∃ x, c x = x ∧ v y = v x := by
  have key : ∃ ϖ, c ϖ = ϖ ∧ v ϖ = v π := by
    by_contra h
    push Not at h
    have h1 : v (π + c π) < v π :=
      lt_of_le_of_ne (v.map_add_le le_rfl (hv π).le) (h _ (by rw [map_add, hc, add_comm]))
    have h0 : v (a * π) ≤ v π := by rw [map_mul]; exact mul_le_of_le_one_left' ha
    have h2 : v (a * π + c (a * π)) < v π :=
      lt_of_le_of_ne (v.map_add_le h0 ((hv _).le.trans h0)) (h _ (by rw [map_add, hc, add_comm]))
    have h3 : v (c a * (π + c π)) < v π := by
      rw [map_mul, hv]; exact lt_of_le_of_lt (mul_le_of_le_one_left' ha) h1
    have h4 := v.map_sub_lt h2 h3
    rw [show a * π + c (a * π) - c a * (π + c π) = (a - c a) * π by rw [map_mul]; ring, map_mul, hd,
      one_mul] at h4
    exact lt_irrefl _ h4
  obtain ⟨ϖ, h1, h2⟩ := key
  by_cases hy : y = 0
  · exact ⟨0, map_zero _, by rw [hy]⟩
  refine ⟨ϖ ^ (-log (v y)), by rw [map_zpow₀, h1], ?_⟩
  rw [map_zpow₀, h2, hπ, ← exp_zsmul]
  simp [exp_log ((Valuation.ne_zero_iff v).2 hy)]

noncomputable def absOfVal {E : Type} [Field E] (v : Valuation E (WithZero (Multiplicative ℤ))) :
    AbsoluteValue E ℝ where
  toFun x := WithZeroMulInt.toNNReal (e := 2) two_ne_zero (v x)
  map_mul' x y := by simp
  nonneg' x := NNReal.coe_nonneg _
  eq_zero' x := by simp
  add_le' x y := by
    have hm := (WithZeroMulInt.toNNReal_strictMono (e := 2) one_lt_two).monotone
    rcases le_max_iff.1 (v.map_add x y) with h | h
    · exact (NNReal.coe_le_coe.2 (hm h)).trans (le_add_of_nonneg_right (NNReal.coe_nonneg _))
    · exact (NNReal.coe_le_coe.2 (hm h)).trans (le_add_of_nonneg_left (NNReal.coe_nonneg _))

theorem absOfVal_le_iff {E : Type} [Field E] (v : Valuation E (WithZero (Multiplicative ℤ))) (x y : E) :
    absOfVal v x ≤ absOfVal v y ↔ v x ≤ v y :=
  NNReal.coe_le_coe.trans (WithZeroMulInt.toNNReal_strictMono (e := 2) one_lt_two).le_iff_le

theorem absOfVal_congr {E : Type} [Field E] (v : Valuation E (WithZero (Multiplicative ℤ))) {x y : E}
    (h : v x = v y) : absOfVal v x = absOfVal v y :=
  le_antisymm ((absOfVal_le_iff v _ _).2 h.le) ((absOfVal_le_iff v _ _).2 h.ge)

end GlobalTheory.UnitLemma.Bridge

namespace GlobalTheory.UnitLemma
open Bridge

theorem UQ.exists_unram : ∀ K : UQ, ∃ (F : Type) (_ : NontriviallyNormedField F) (nE : NontriviallyNormedField K.E) (hE : nE.toField = K.fE) (_ : @NormedAlgebra F K.E _ nE.toNormedField.toNormedCommRing.toSeminormedCommRing.toSeminormedRing) (st : @StarRing K.E nE.toNormedField.toNormedCommRing.toRing.toNonAssocRing.toNonUnitalNonAssocRing.toNonUnitalNonAssocSemiring), @GlobalTheory.JR.Unram F K.E _ nE _ st ∧ (∀ y, st.star y = K.c y) ∧ ∀ y : K.E, nE.norm y ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range := by
  intro K
  let v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E
  have hint : ∀ y : K.E, v y ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range := by
    intro y
    refine ⟨fun h => IsDiscreteValuationRing.exists_lift_of_le_one h, ?_⟩
    rintro ⟨a, rfl⟩
    exact (IsDiscreteValuationRing.maximalIdeal K.O).valuation_le_one a
  have hle : ∀ y, v y ≤ 1 → v (K.c y) ≤ 1 := by
    intro y hy
    obtain ⟨a, rfl⟩ := (hint y).1 hy
    obtain ⟨b, hb⟩ := K.c_int a
    exact (hint _).2 ⟨b, hb.symm⟩
  have hv := val_conj v π hπ K.c K.c_c hle
  obtain ⟨a, b, hab, hm⟩ := K.c_res
  have hd : v (algebraMap K.O K.E a - K.c (algebraMap K.O K.E a)) = 1 := by
    rw [hab, ← map_sub]
    refine le_antisymm ((hint _).2 ⟨_, rfl⟩) (not_lt.1 fun h => hm ?_)
    exact ((IsDiscreteValuationRing.maximalIdeal K.O).valuation_lt_one_iff_mem _).1 h
  have hu := exists_fixed_val v π hπ K.c K.c_c hv _ ((hint _).2 ⟨a, rfl⟩) hd
  have hne : ∃ y, K.c y ≠ y := by
    refine ⟨algebraMap K.O K.E a, fun h => ?_⟩
    rw [h, sub_self, map_zero] at hd
    exact zero_ne_one hd
  have hball : ∀ y : K.E, absOfVal v y ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range := by
    intro y
    rw [← hint, ← (absOfVal v).map_one, absOfVal_le_iff, map_one]
  letI nE : NontriviallyNormedField K.E :=
    { (absOfVal v).toNormedField with
      non_trivial := by
        refine ⟨π⁻¹, not_le.1 fun h => ?_⟩
        have h1 : absOfVal v π⁻¹ ≤ 1 := h
        rw [hball, ← hint, map_inv₀] at h1
        rw [show v π = WithZero.exp (-1) from hπ, ← WithZero.exp_neg, ← WithZero.exp_zero,
          WithZero.exp_le_exp] at h1
        omega }
  haveI : IsUltrametricDist K.E := IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    fun x y => by
      change absOfVal v (x + y) ≤ max (absOfVal v x) (absOfVal v y)
      rw [le_max_iff, absOfVal_le_iff, absOfVal_le_iff, ← le_max_iff]
      exact v.map_add x y
  haveI : LocallyCompactSpace K.E :=
    locallyCompact_of_complete (O := K.O) (IsFractionRing.injective K.O K.E) hball
  obtain ⟨F, nF, nA, st, h1, h2⟩ := unram_of_involution (nE := nE) K.c K.c_c hne
    (fun y => absOfVal_congr v (hv y))
    (fun y => (hu y).imp fun x hx => ⟨hx.1, absOfVal_congr v hx.2⟩)
  exact ⟨F, nF, nE, rfl, nA, st, h1, h2, hball⟩

end GlobalTheory.UnitLemma
