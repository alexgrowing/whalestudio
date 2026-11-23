import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.NormalisedValue

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem val_pi_lt_one (h : LF O ϖ nrm q) : ValuativeRel.valuation F ϖ < 1 := by
  exact (h.lt_one ϖ).2 ⟨1, O.one_mem, (mul_one ϖ).symm⟩

theorem val_pi_pos (h : LF O ϖ nrm q) : 0 < ValuativeRel.valuation F ϖ := by
  first
    | exact (Valuation.pos_iff _).2 h.ne
    | exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h.ne)

theorem mem_iff_val_le (h : LF O ϖ nrm q) (x : F) : x ∈ O ↔ ValuativeRel.valuation F x ≤ 1 := by
  rw [h.O_eq]
  exact Valuation.mem_integer_iff _ _

theorem one_lt_q (h : LF O ϖ nrm q) : 1 < q := by
  have hq0 : q ≠ 0 := by
    intro hq
    have hp := h.nrm_pi
    rw [hq, Nat.cast_zero, _root_.inv_zero] at hp
    exact h.ne ((AbsoluteValue.eq_zero nrm).1 hp)
  have hq1 : q ≠ 1 := by
    intro hq
    have hc := h.card
    rw [hq] at hc
    have hs := (Nat.card_eq_one_iff_unique.1 hc.symm).1
    exact not_subsingleton (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) hs
  omega

private theorem isUnit_iff_valuation_eq_one' (y : 𝒪[F]) : IsUnit y ↔ ValuativeRel.valuation F (y : F) = 1 := by
  first
    | exact (Valuation.integer.integers _).isUnit_iff_valuation_eq_one
    | simpa using (Valuation.integer.integers (ValuativeRel.valuation F)).isUnit_iff_valuation_eq_one (x := y)

theorem irreducible_pi (h : LF O ϖ nrm q) :
    Irreducible (⟨ϖ, (Valuation.mem_integer_iff _ _).2 (val_pi_lt_one h).le⟩ : 𝒪[F]) := by
  refine ⟨?_, ?_⟩
  · rw [isUnit_iff_valuation_eq_one']
    exact (val_pi_lt_one h).ne
  · intro a b hab
    by_cases ha : ValuativeRel.valuation F (a : F) = 1
    · left
      exact (isUnit_iff_valuation_eq_one' a).2 ha
    · right
      have ha1 : ValuativeRel.valuation F (a : F) < 1 :=
        lt_of_le_of_ne ((Valuation.mem_integer_iff _ _).1 a.2) ha
      obtain ⟨o, hoO, hao⟩ := (h.lt_one a).1 ha1
      have hab' : (ϖ : F) = (a : F) * (b : F) := congrArg Subtype.val hab
      have hoI : o ∈ 𝒪[F] := by
        rw [← h.O_eq]
        exact hoO
      have hob : (⟨o, hoI⟩ : 𝒪[F]) * b = 1 := by
        apply Subtype.ext
        show o * (b : F) = 1
        have hh : ϖ * 1 = ϖ * (o * (b : F)) := by
          rw [mul_one, ← mul_assoc, ← hao, ← hab']
        exact (mul_left_cancel₀ h.ne hh).symm
      exact ⟨⟨b, ⟨o, hoI⟩, (mul_comm _ _).trans hob, hob⟩, rfl⟩

theorem val_eq_pow_of_int (h : LF O ϖ nrm q) {x : F} (hx : x ≠ 0)
    (hxO : ValuativeRel.valuation F x ≤ 1) :
    ∃ n : ℕ, ValuativeRel.valuation F x = ValuativeRel.valuation F ϖ ^ n := by
  have hxI : x ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).2 hxO
  have hx' : (⟨x, hxI⟩ : 𝒪[F]) ≠ 0 := by
    intro h0
    exact hx (congrArg Subtype.val h0)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx' (irreducible_pi h)
  refine ⟨n, ?_⟩
  have hv := congrArg (fun y : 𝒪[F] => ValuativeRel.valuation F (y : F)) hu
  have hu1 : ValuativeRel.valuation F ((u : 𝒪[F]) : F) = 1 := (isUnit_iff_valuation_eq_one' _).1 u.isUnit
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hu1, one_mul] at hv
  exact hv

theorem val_eq_zpow (h : LF O ϖ nrm q) {x : F} (hx : x ≠ 0) :
    ∃ e : ℤ, ValuativeRel.valuation F x = ValuativeRel.valuation F ϖ ^ e := by
  by_cases hle : ValuativeRel.valuation F x ≤ 1
  · obtain ⟨n, hn⟩ := val_eq_pow_of_int h hx hle
    exact ⟨n, by rw [hn, _root_.zpow_natCast]⟩
  · have hlt : 1 < ValuativeRel.valuation F x := lt_of_not_ge hle
    have hinv : ValuativeRel.valuation F x⁻¹ ≤ 1 := ((Valuation.one_lt_val_iff _ hx).1 hlt).le
    obtain ⟨n, hn⟩ := val_eq_pow_of_int h (inv_ne_zero hx) hinv
    refine ⟨-(n : ℤ), ?_⟩
    rw [_root_.zpow_neg, _root_.zpow_natCast, ← hn, map_inv₀, _root_.inv_inv]

theorem val_mul_zpow (h : LF O ϖ nrm q) {x : F} {e : ℤ}
    (he : ValuativeRel.valuation F x = ValuativeRel.valuation F ϖ ^ e) :
    ValuativeRel.valuation F (x * ϖ ^ (-e)) = 1 := by
  rw [map_mul, map_zpow₀, he, ← zpow_add₀ (val_pi_pos h).ne']
  simp

theorem nrm_eq_zpow (h : LF O ϖ nrm q) {x : F} {e : ℤ}
    (he : ValuativeRel.valuation F x = ValuativeRel.valuation F ϖ ^ e) :
    nrm x = (q : ℝ) ^ (-e) := by
  have h1 : nrm (x * ϖ ^ (-e)) = 1 := h.nrm_unit _ (val_mul_zpow h he)
  have hdecomp : x = x * ϖ ^ (-e) * ϖ ^ e := by
    rw [mul_assoc, ← zpow_add₀ h.ne, neg_add_cancel, _root_.zpow_zero, mul_one]
  have hz : nrm (ϖ ^ e) = nrm ϖ ^ e := by
    first
      | exact map_zpow₀ nrm ϖ e
      | exact map_zpow₀ nrm.toMonoidWithZeroHom ϖ e
  conv_lhs => rw [hdecomp]
  rw [map_mul, h1, one_mul, hz, h.nrm_pi, _root_.inv_zpow']

private theorem nrm_le_one_of_valuation_le_one (h : LF O ϖ nrm q) (x : F) (hx : ValuativeRel.valuation F x ≤ 1) :
    nrm x ≤ 1 := by
  by_cases h0 : x = 0
  · simp [h0]
  · obtain ⟨n, hn⟩ := val_eq_pow_of_int h h0 hx
    rw [nrm_eq_zpow h (e := (n : ℤ)) (by rw [hn, _root_.zpow_natCast]), _root_.zpow_neg, _root_.zpow_natCast]
    have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (one_lt_q h).le
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hq)

private theorem nrm_le_inv_q_of_valuation_lt_one (h : LF O ϖ nrm q) (x : F) (hx : ValuativeRel.valuation F x < 1) :
    nrm x ≤ (q : ℝ)⁻¹ := by
  obtain ⟨o, hoO, rfl⟩ := (h.lt_one x).1 hx
  rw [map_mul, h.nrm_pi]
  have ho : nrm o ≤ 1 := nrm_le_one_of_valuation_le_one h o ((mem_iff_val_le h o).1 hoO)
  have hq : (0 : ℝ) ≤ (q : ℝ)⁻¹ := by positivity
  calc (q : ℝ)⁻¹ * nrm o ≤ (q : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left ho hq
    _ = (q : ℝ)⁻¹ := mul_one _

theorem nrm_le_one_iff (h : LF O ϖ nrm q) (x : F) :
    nrm x ≤ 1 ↔ ValuativeRel.valuation F x ≤ 1 := by
  constructor
  · intro hn
    by_contra hv
    have hlt : 1 < ValuativeRel.valuation F x := lt_of_not_ge hv
    have hx : x ≠ 0 := by
      rintro rfl
      simp at hlt
    have hi : ValuativeRel.valuation F x⁻¹ < 1 := (Valuation.one_lt_val_iff _ hx).1 hlt
    have h2 : nrm x⁻¹ ≤ (q : ℝ)⁻¹ := nrm_le_inv_q_of_valuation_lt_one h _ hi
    have hq : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast one_lt_q h)
    rw [map_inv₀] at h2
    have hpos : 0 < nrm x := nrm.pos hx
    have h3 : (nrm x)⁻¹ < 1 := lt_of_le_of_lt h2 hq
    have h4 : 1 < nrm x := (inv_lt_one₀ hpos).1 h3
    linarith
  · exact nrm_le_one_of_valuation_le_one h x

theorem nrm_lt_one_iff (h : LF O ϖ nrm q) (x : F) :
    nrm x < 1 ↔ ValuativeRel.valuation F x < 1 := by
  constructor
  · intro hn
    by_contra hv
    have h1 : 1 ≤ ValuativeRel.valuation F x := not_lt.1 hv
    rcases h1.lt_or_eq with hlt | heq
    · exact absurd ((nrm_le_one_iff h x).1 hn.le) (not_le.2 hlt)
    · have hu := h.nrm_unit x heq.symm
      linarith
  · intro hv
    exact lt_of_le_of_lt (nrm_le_inv_q_of_valuation_lt_one h x hv) (inv_lt_one_of_one_lt₀ (by exact_mod_cast one_lt_q h))

theorem nrm_le_of_val_le (h : LF O ϖ nrm q) {x y : F}
    (hxy : ValuativeRel.valuation F x ≤ ValuativeRel.valuation F y) : nrm x ≤ nrm y := by
  by_cases hy : y = 0
  · have hv0 : ValuativeRel.valuation F x = 0 := by
      rw [hy, map_zero] at hxy
      exact le_antisymm hxy zero_le
    have hx : x = 0 := (Valuation.zero_iff _).1 hv0
    simp [hx]
  · have hyv : ValuativeRel.valuation F y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
    have hq : ValuativeRel.valuation F (x * y⁻¹) ≤ 1 := by
      rw [map_mul, map_inv₀]
      calc ValuativeRel.valuation F x * (ValuativeRel.valuation F y)⁻¹
          ≤ ValuativeRel.valuation F y * (ValuativeRel.valuation F y)⁻¹ := by gcongr
        _ = 1 := _root_.mul_inv_cancel₀ hyv
    have h1 := (nrm_le_one_iff h _).2 hq
    rw [map_mul, map_inv₀] at h1
    have hpos : 0 < nrm y := nrm.pos hy
    calc nrm x = nrm x * (nrm y)⁻¹ * nrm y := (_root_.inv_mul_cancel_right₀ hpos.ne' _).symm
      _ ≤ 1 * nrm y := mul_le_mul_of_nonneg_right h1 hpos.le
      _ = nrm y := one_mul _

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → 1 < q ∧ ϖ ∈ O ∧ (∀ x : F, nrm x ≤ 1 ↔ x ∈ O) ∧ (∀ x : F, nrm x < 1 ↔ ∃ o ∈ O, x = ϖ * o) ∧ (∀ x : F, x ≠ 0 → ∃ e : ℤ, nrm x = (q : ℝ) ^ (-e) ∧ nrm (x * ϖ ^ (-e)) = 1) ∧ (∀ x y : F, nrm (x + y) ≤ max (nrm x) (nrm y)) ∧ (∀ x : F, nrm x = 1 ↔ ValuativeRel.valuation F x = 1) := by
  intro F _ _ _ _ O ϖ nrm q h
  refine ⟨one_lt_q h, (mem_iff_val_le h ϖ).2 (val_pi_lt_one h).le,
    fun x => (nrm_le_one_iff h x).trans (mem_iff_val_le h x).symm,
    fun x => (nrm_lt_one_iff h x).trans (h.lt_one x), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨e, he⟩ := val_eq_zpow h hx
    exact ⟨e, nrm_eq_zpow h he, h.nrm_unit _ (val_mul_zpow h he)⟩
  · intro x y
    rcases le_total (ValuativeRel.valuation F x) (ValuativeRel.valuation F y) with hxy | hxy
    · have hs : ValuativeRel.valuation F (x + y) ≤ ValuativeRel.valuation F y :=
        le_trans (Valuation.map_add _ x y) (max_le hxy le_rfl)
      exact le_trans (nrm_le_of_val_le h hs) (le_max_right _ _)
    · have hs : ValuativeRel.valuation F (x + y) ≤ ValuativeRel.valuation F x :=
        le_trans (Valuation.map_add _ x y) (max_le le_rfl hxy)
      exact le_trans (nrm_le_of_val_le h hs) (le_max_left _ _)
  · intro x
    constructor
    · intro hn
      have h1 := (nrm_le_one_iff h x).1 hn.le
      have h2 : ¬ ValuativeRel.valuation F x < 1 := fun hlt => by
        have := (nrm_lt_one_iff h x).2 hlt
        linarith
      exact le_antisymm h1 (not_lt.1 h2)
    · exact h.nrm_unit x

end GlobalTheory.CompanionTheory.QL.NormalisedValue
