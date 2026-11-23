import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.IsHerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace UpperTheory.G3.FixRing

section Abstract

variable {O : Type} [CommRing O]

private abbrev S (c : O →+* O) : Subring O := c.eqLocus (RingHom.id O)

private noncomputable def cE (c : O →+* O) (hc : ∀ x, c (c x) = x) : O ≃ₐ[S c] O :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom c c (RingHom.ext hc) (RingHom.ext hc)) (fun r => r.2)

private theorem cE_apply (c : O →+* O) (hc : ∀ x, c (c x) = x) (x : O) : cE c hc x = c x := rfl

private theorem isGal_cE (c : O →+* O) (hc : ∀ x, c (c x) = x) (ω u : O) (hu : (ω - c ω) * u = 1) :
    UpperTheory.ConvolutionTheory.D.IsGal (cE c hc) 2 where
  pos := by norm_num
  pow := by
    ext x
    rw [pow_two, AlgEquiv.mul_apply, cE_apply, cE_apply, hc, AlgEquiv.one_apply]
  inj := Subtype.val_injective
  fix := fun r hr => ⟨⟨r, hr⟩, rfl⟩
  sep := by
    refine ⟨2, ![-(c ω) * u, u], ![1, ω], fun j hj => ?_⟩
    interval_cases j
    · simp only [Fin.sum_univ_two, pow_zero, AlgEquiv.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one, if_true]
      linear_combination hu
    · simp only [Fin.sum_univ_two, pow_one, cE_apply, Matrix.cons_val_zero, Matrix.cons_val_one, map_one]
      simp
      ring

private theorem isUnit_S (c : O →+* O) (a : S c) (h : IsUnit (a : O)) : IsUnit a := by
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 h
  have ha : c (a : O) = a := a.2
  have h1 : (a : O) * c b = 1 := by
    have := congrArg c hb
    rwa [map_mul, ha, map_one] at this
  have hcb : c b = b := by
    calc c b = (b * a) * c b := by rw [mul_comm b, hb, one_mul]
      _ = b * (a * c b) := by ring
      _ = b := by rw [h1, mul_one]
  exact isUnit_iff_exists_inv.2 ⟨⟨b, hcb⟩, Subtype.ext hb⟩

private theorem isLocal_S [Nontrivial O] (c : O →+* O) (h : ∀ x : O, IsUnit x ∨ IsUnit (1 - x)) :
    IsLocalRing (S c) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases h a with h | h
  · exact Or.inl (isUnit_S c a h)
  · exact Or.inr (isUnit_S c (1 - a) (by simpa using h))

end Abstract

section Val

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

private theorem le_iff_mul_inv {x b : L} (hb : b ≠ 0) :
    Valued.v (x * b⁻¹) ≤ 1 ↔ Valued.v x ≤ Valued.v b := by
  rw [map_mul, map_inv₀, ← div_eq_mul_inv, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb))]

private theorem sub_le {g : ℕ → L} {a : L} (ha : Valued.v a ≤ 1)
    (hg : ∀ m, Valued.v (g (m + 1) - g m) ≤ Valued.v a ^ m) (m n : ℕ) (hmn : m ≤ n) :
    Valued.v (g n - g m) ≤ Valued.v a ^ m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have e : g (n + 1) - g m = (g (n + 1) - g n) + (g n - g m) := by ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le ((hg n).trans (pow_le_pow_right_of_le_one' ha hmn)) ih)

private theorem exists_limit [CompleteSpace L] {a : L} (ha0 : a ≠ 0) (ha : Valued.v a < 1) {g : ℕ → L}
    (hg : ∀ m, Valued.v (g (m + 1) - g m) ≤ Valued.v a ^ m) :
    ∃ l, ∀ m, Valued.v (g m - l) ≤ Valued.v a ^ m := by
  have hc : CauchySeq g := by
    rw [(Valued.hasBasis_uniformity L _).cauchySeq_iff]
    intro γ _
    have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
    obtain ⟨N, hN⟩ := exists_pow_lt₀ ha (Units.mk0 _ hne)
    have key : ∀ p r, N ≤ p → p ≤ r → Valued.v (g r - g p) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 :=
      fun p r hp hpr => lt_of_le_of_lt ((sub_le ha.le hg p r hpr).trans
        (pow_le_pow_right_of_le_one' ha.le hp)) hN
    refine ⟨N, fun m hm n hn => ?_⟩
    simp only [Set.mem_setOf_eq]
    rw [Valuation.restrict_lt_iff_lt_embedding]
    rcases le_total m n with h | h
    · exact key m n hm h
    · rw [Valuation.map_sub_swap]
      exact key n m hn h
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨l, fun m => ?_⟩
  have hb : a ^ m ≠ 0 := pow_ne_zero _ ha0
  have hcl : IsClosed {y : L | Valued.v ((g m - y) * (a ^ m)⁻¹) ≤ 1} :=
    (Valued.isClosed_integer (R := L)).preimage
      (f := fun y : L => (g m - y) * (a ^ m)⁻¹) (by fun_prop)
  have hmem : Valued.v ((g m - l) * (a ^ m)⁻¹) ≤ 1 := by
    refine hcl.mem_of_tendsto hl ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    show Valued.v ((g m - g n) * (a ^ m)⁻¹) ≤ 1
    rw [le_iff_mul_inv hb, Valuation.map_sub_swap, map_pow]
    exact sub_le ha.le hg m n hn
  rw [le_iff_mul_inv hb, map_pow] at hmem
  exact hmem

private theorem isUnit_int_iff (x : intL L) : IsUnit x ↔ Valued.v (x : L) = 1 := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 h
    have h1 : Valued.v (x : L) * Valued.v (b : L) = 1 := by
      rw [← map_mul, ← Subring.coe_mul, hb]
      simp
    have hx : Valued.v (x : L) ≤ 1 := x.2
    have hb' : Valued.v (b : L) ≤ 1 := b.2
    by_contra hne
    have hlt : Valued.v (x : L) < 1 := lt_of_le_of_ne hx hne
    exact absurd h1 (ne_of_lt (lt_of_le_of_lt (mul_le_of_le_one_right' hb') hlt))
  · intro h
    have hne : (x : L) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h
      exact zero_ne_one h
    refine isUnit_iff_exists_inv.2 ⟨⟨(x : L)⁻¹, ?_⟩, Subtype.ext ?_⟩
    · show Valued.v (x : L)⁻¹ ≤ 1
      rw [map_inv₀, h, inv_one]
    · simp [hne]

private theorem isUnit_or (x : intL L) : IsUnit x ∨ IsUnit (1 - x) := by
  by_cases h : Valued.v (x : L) = 1
  · exact Or.inl ((isUnit_int_iff x).2 h)
  · have hlt : Valued.v (x : L) < 1 := lt_of_le_of_ne x.2 h
    refine Or.inr ((isUnit_int_iff _).2 ?_)
    have : (((1 - x : intL L)) : L) = 1 - (x : L) := by simp
    rw [this]
    exact Valuation.map_one_sub_of_lt _ hlt

private theorem t_lt_one :
    ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]
  norm_num

private theorem valuation_lt_one_le_uniformiser {a : WithZero (Multiplicative ℤ)} (h : a < 1) :
    a ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact zero_le'
  · obtain ⟨b, rfl⟩ := WithZero.ne_zero_iff_exists.1 ha
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h
    rw [WithZero.coe_le_coe]
    have h' : Multiplicative.toAdd b < 0 := h
    show Multiplicative.toAdd b ≤ -1
    omega

end Val

section Main

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

private theorem span_eq {ϖ : L} (hv : Valued.v ϖ =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (p : intL L) (hp : (p : L) = ϖ) :
    Ideal.span {p} = (IsLocalRing.maximalIdeal
      (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring : Ideal (intL L)) := by
  have hp1 : Valued.v (p : L) < 1 := by rw [hp, hv]; exact t_lt_one
  have hp0 : (p : L) ≠ 0 := by
    intro h0
    rw [hp] at h0
    rw [h0, map_zero] at hv
    exact WithZero.zero_ne_coe hv
  ext x
  rw [Ideal.mem_span_singleton]
  change _ ↔ x ∈ nonunits _
  constructor
  · rintro ⟨e, rfl⟩ hu
    have hu' : IsUnit (p * e) := hu
    have := (isUnit_int_iff _).1 (isUnit_of_mul_isUnit_left hu')
    exact absurd this (ne_of_lt hp1)
  · intro hx
    have hx' : ¬ IsUnit x := hx
    have hlt : Valued.v (x : L) < 1 :=
      lt_of_le_of_ne x.2 (fun h => hx' ((isUnit_int_iff x).2 h))
    have hle : Valued.v (x : L) ≤ Valued.v (p : L) := by
      rw [hp, hv]
      exact valuation_lt_one_le_uniformiser hlt
    refine ⟨⟨(x : L) * (p : L)⁻¹, (le_iff_mul_inv hp0).2 hle⟩, Subtype.ext ?_⟩
    simp only [Subring.coe_mul]
    field_simp

theorem fixed_ring_data [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) :
    ∃ (k : Type) (_ : CommRing k) (_ : IsLocalRing k) (_ : Algebra k (intL L))
      (c : intL L ≃ₐ[k] intL L) (p ω : intL L),
      UpperTheory.ConvolutionTheory.D.IsGal c 2 ∧ (∀ x : intL L, ((c x : intL L) : L) = σ x) ∧ c p = p ∧ p ≠ 0 ∧
      (∀ f : ℕ → intL L, (∀ m, ∃ e, f (m + 1) - f m = p ^ m * e) → ∃ l, ∀ m, ∃ e, f m - l = p ^ m * e) ∧
      (∀ x : intL L, (∀ m : ℕ, ∃ e, x = p ^ m * e) → x = 0) ∧
      Finite (intL L ⧸ Ideal.span {p}) ∧ IsUnit (ω - c ω) := by
  obtain ⟨hinv, hval, hfix, hv, ⟨x0, hx0, hx1⟩, hq, hcard⟩ := h
  have hlt : Valued.v ϖ < 1 := by rw [hv]; exact t_lt_one
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact WithZero.zero_ne_coe hv
  let c0 : intL L →+* intL L := σ.restrict (intL L) (intL L) (fun x hx => by
    show Valued.v (σ x) ≤ 1
    rw [hval]
    exact hx)
  have hc0 : ∀ x : intL L, ((c0 x : intL L) : L) = σ x := fun _ => rfl
  have hc : ∀ x, c0 (c0 x) = x := fun x => Subtype.ext (by rw [hc0, hc0, hinv])
  let p : intL L := ⟨ϖ, hlt.le⟩
  let ω : intL L := ⟨x0, hx0⟩
  have hω : IsUnit (ω - c0 ω) := by
    refine (isUnit_int_iff _).2 ?_
    have : (((ω - c0 ω : intL L)) : L) = x0 - σ x0 := rfl
    rw [this, Valuation.map_sub_swap]
    exact hx1
  obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.1 hω
  have hp1 : ∀ (m : ℕ) (e : intL L), Valued.v (((p ^ m * e : intL L)) : L) ≤ Valued.v ϖ ^ m := by
    intro m e
    have : (((p ^ m * e : intL L)) : L) = ϖ ^ m * (e : L) := rfl
    rw [this, map_mul, map_pow]
    exact mul_le_of_le_one_right' e.2
  refine ⟨S c0, inferInstance, isLocal_S c0 isUnit_or, inferInstance, cE c0 hc, p, ω,
    isGal_cE c0 hc ω u hu, hc0, Subtype.ext hfix, fun h0 => hϖ0 (congrArg Subtype.val h0), ?_, ?_, ?_, hω⟩
  · intro f hf
    have hg : ∀ m, Valued.v ((f (m + 1) : L) - (f m : L)) ≤ Valued.v ϖ ^ m := by
      intro m
      obtain ⟨e, he⟩ := hf m
      have := hp1 m e
      rwa [← he] at this
    obtain ⟨l, hl'⟩ := exists_limit (g := fun m => (f m : L)) hϖ0 hlt hg
    have hl : ∀ m, Valued.v ((f m : L) - l) ≤ Valued.v ϖ ^ m := hl'
    have hl1 : Valued.v l ≤ 1 := by
      have h0 := hl 0
      rw [pow_zero] at h0
      have e : l = (f 0 : L) - ((f 0 : L) - l) := by ring
      rw [e]
      exact (Valuation.map_sub _ _ _).trans (max_le (f 0).2 h0)
    refine ⟨⟨l, hl1⟩, fun m => ?_⟩
    have hb : ϖ ^ m ≠ 0 := pow_ne_zero _ hϖ0
    refine ⟨⟨((f m : L) - l) * (ϖ ^ m)⁻¹, (le_iff_mul_inv hb).2 (by rw [map_pow]; exact hl m)⟩, Subtype.ext ?_⟩
    show (f m : L) - l = ϖ ^ m * (((f m : L) - l) * (ϖ ^ m)⁻¹)
    field_simp
  · intro x hx
    by_contra hne
    have hx0' : Valued.v (x : L) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (fun h0 => hne (Subtype.ext h0))
    obtain ⟨N, hN⟩ := exists_pow_lt₀ hlt (Units.mk0 _ hx0')
    obtain ⟨e, he⟩ := hx N
    have := hp1 N e
    rw [← he] at this
    exact absurd (lt_of_le_of_lt this hN) (lt_irrefl _)
  · have hfin : Finite ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸
        IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
    rw [span_eq hv p rfl]
    exact hfin

end Main

end UpperTheory.G3.FixRing

theorem UpperTheory.exists_local_quadratic_galois_data_at_nonsplit_place :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, ¬ IsSplitAt w →
        ∃ (k : Type) (_ : CommRing k) (_ : IsLocalRing k) (_ : Algebra k (Ov E w)) (c : Ov E w ≃ₐ[k] Ov E w) (ϖ ω : Ov E w),
          UpperTheory.ConvolutionTheory.D.IsGal c 2 ∧ (∀ x : Ov E w, ((c x : Ov E w) : w.adicCompletion E) = cj w x) ∧ c ϖ = ϖ ∧ ϖ ≠ 0 ∧
          (∀ f : ℕ → Ov E w, (∀ m, ∃ e, f (m + 1) - f m = ϖ ^ m * e) → ∃ L, ∀ m, ∃ e, f m - L = ϖ ^ m * e) ∧
          (∀ x : Ov E w, (∀ m : ℕ, ∃ e, x = ϖ ^ m * e) → x = 0) ∧
          Finite (Ov E w ⧸ Ideal.span {ϖ}) ∧ IsUnit (ω - c ω) := by
  intro E _ _ _ hU w hw
  obtain ⟨ϖ, q, hq, -⟩ := ((GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.2.1 hw).2.1
  exact UpperTheory.G3.FixRing.fixed_ring_data hq
