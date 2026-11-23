import Mathlib
import Formalism.SatakeDualWeyl.StatementF
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOneAddPiOMul
import GroundTheory.LocalFields.FilteredSurj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulInvolEqOfFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedAdjoinRootOfSeparable
open Polynomial Matrix Formalism.UG

namespace GlobalTheory.NormEq

theorem eq_zero_of_forall_mem_maxSpec {A : Type} [CommRing A] [IsArtinianRing A] [IsReduced A] {y : A}
    (h : ∀ I : MaximalSpectrum A, y ∈ I.asIdeal) : y = 0 := by
  apply (IsArtinianRing.equivPi A).injective
  rw [map_zero]
  funext I
  rw [IsArtinianRing.equivPi_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (h I)

theorem exists_mul_invol_eq_of_fixed_unit {R : Type} [CommRing R] [Finite R] [IsReduced R]
    (τ : R →+* R) (hτ : ∀ a, τ (τ a) = a) {b : R} (hb : IsUnit (τ b - b)) {x : R} (hx : IsUnit x)
    (hxτ : τ x = x) : ∃ z : R, IsUnit z ∧ z * τ z = x := by
  classical
  haveI : IsArtinianRing R := inferInstance
  have hsurj : Function.Surjective τ := fun a => ⟨τ a, hτ a⟩
  obtain ⟨tI, hmem, htt⟩ : ∃ tI : MaximalSpectrum R → MaximalSpectrum R,
      (∀ I y, y ∈ (tI I).asIdeal ↔ τ y ∈ I.asIdeal) ∧ ∀ I, tI (tI I) = I := by
    have hmax : ∀ I : MaximalSpectrum R, (I.asIdeal.comap τ).IsMaximal := fun I => by
      haveI := I.isMaximal
      exact Ideal.comap_isMaximal_of_surjective τ hsurj
    refine ⟨fun I => ⟨I.asIdeal.comap τ, hmax I⟩, fun I y => Iff.rfl, fun I => ?_⟩
    ext y
    change τ (τ y) ∈ I.asIdeal ↔ y ∈ I.asIdeal
    rw [hτ]
  have hnot : ∀ (I : MaximalSpectrum R) {u : R}, IsUnit u → u ∉ I.asIdeal := fun I u hu hI =>
    I.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hI hu)

  have hfixed : ∀ I : MaximalSpectrum R, ∃ a : R, tI I = I → a * τ a - x ∈ I.asIdeal := by
    intro I
    by_cases hI : tI I = I
    · have hle : I.asIdeal ≤ I.asIdeal.comap τ := fun y hy => by
        rw [Ideal.mem_comap, ← hmem, hI]; exact hy
      haveI := I.isMaximal
      letI : Field (R ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
      haveI : Finite (R ⧸ I.asIdeal) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
      let ρ := Ideal.quotientMap I.asIdeal τ hle
      have hρ : ∀ y, ρ (Ideal.Quotient.mk I.asIdeal y) = Ideal.Quotient.mk I.asIdeal (τ y) :=
        fun y => Ideal.quotientMap_mk
      have hinv : Function.Involutive ρ := fun c => by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective c
        rw [hρ, hρ, hτ]
      have hne : ∃ c, ρ c ≠ c := ⟨Ideal.Quotient.mk I.asIdeal b, fun h => by
        rw [hρ, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem] at h
        exact hnot I hb h⟩
      obtain ⟨a', ha'⟩ := GlobalTheory.exists_mul_invol_eq_of_fixed (R ⧸ I.asIdeal) ρ hinv hne
        (Ideal.Quotient.mk I.asIdeal x) (by rw [hρ, hxτ])
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
      refine ⟨a, fun _ => ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hρ, ha', sub_self]
    · exact ⟨0, fun h => absurd h hI⟩
  choose a ha using hfixed
  let r : MaximalSpectrum R → R := fun I =>
    if WellOrderingRel I (tI I) then x else if WellOrderingRel (tI I) I then 1 else a I
  obtain ⟨z, hz⟩ : ∃ z : R, ∀ I, z - r I ∈ I.asIdeal := by
    refine ⟨(IsArtinianRing.equivPi R).symm (fun I => Ideal.Quotient.mk I.asIdeal (r I)), fun I => ?_⟩
    have h1 := congrFun ((IsArtinianRing.equivPi R).apply_symm_apply
      (fun I => Ideal.Quotient.mk I.asIdeal (r I))) I
    rw [IsArtinianRing.equivPi_apply] at h1
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, sub_self]
  have hτz : ∀ I, τ z - τ (r (tI I)) ∈ I.asIdeal := fun I => by
    rw [← map_sub, ← hmem]; exact hz (tI I)
  have hfix_of : ∀ I, ¬ WellOrderingRel I (tI I) → ¬ WellOrderingRel (tI I) I → tI I = I := fun I h1 h2 => by
    rcases trichotomous_of WellOrderingRel I (tI I) with h | h | h
    · exact absurd h h1
    · exact h.symm
    · exact absurd h h2
  have key : ∀ I : MaximalSpectrum R, z * τ z - x ∈ I.asIdeal ∧ z ∉ I.asIdeal := by
    intro I
    have hzI := hz I
    have hτzI := hτz I
    by_cases h1 : WellOrderingRel I (tI I)
    · have e1 : r I = x := if_pos h1
      have e2 : r (tI I) = 1 := by
        simp only [r, htt]
        rw [if_neg (asymm_of WellOrderingRel h1), if_pos h1]
      rw [e1] at hzI
      rw [e2, map_one] at hτzI
      refine ⟨?_, fun hzm => hnot I hx (by simpa using I.asIdeal.sub_mem hzm hzI)⟩
      have : z * τ z - x = (z - x) * τ z + x * (τ z - 1) := by ring
      rw [this]
      exact I.asIdeal.add_mem (I.asIdeal.mul_mem_right _ hzI) (I.asIdeal.mul_mem_left _ hτzI)
    · by_cases h2 : WellOrderingRel (tI I) I
      · have e1 : r I = 1 := by simp only [r]; rw [if_neg h1, if_pos h2]
        have e2 : r (tI I) = x := by
          simp only [r, htt]
          rw [if_pos h2]
        rw [e1] at hzI
        rw [e2, hxτ] at hτzI
        refine ⟨?_, fun hzm => hnot I isUnit_one (by simpa using I.asIdeal.sub_mem hzm hzI)⟩
        have : z * τ z - x = (z - 1) * τ z + (τ z - x) := by ring
        rw [this]
        exact I.asIdeal.add_mem (I.asIdeal.mul_mem_right _ hzI) hτzI
      · have hI := hfix_of I h1 h2
        have e1 : r I = a I := by simp only [r]; rw [if_neg h1, if_neg h2]
        rw [e1] at hzI
        rw [hI, e1] at hτzI
        have haI := ha I hI
        refine ⟨?_, fun hzm => ?_⟩
        · have : z * τ z - x = (z - a I) * τ z + a I * (τ z - τ (a I)) + (a I * τ (a I) - x) := by ring
          rw [this]
          exact I.asIdeal.add_mem (I.asIdeal.add_mem (I.asIdeal.mul_mem_right _ hzI)
            (I.asIdeal.mul_mem_left _ hτzI)) haI
        · have haM : a I ∈ I.asIdeal := by simpa using I.asIdeal.sub_mem hzm hzI
          exact hnot I hx (by simpa using I.asIdeal.sub_mem (I.asIdeal.mul_mem_right (τ (a I)) haM) haI)
  refine ⟨z, ?_, sub_eq_zero.1 (eq_zero_of_forall_mem_maxSpec fun I => (key I).1)⟩
  by_contra hu
  obtain ⟨M, hM, hzM⟩ := exists_max_ideal_of_mem_nonunits (show z ∈ nonunits R from hu)
  exact (key ⟨M, hM⟩).2 hzM

end GlobalTheory.NormEq

namespace GlobalTheory.NormEq

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mul_ofAdd_one_le_of_lt_one {a : WithZero (Multiplicative ℤ)} (ha : a < 1) :
    a * ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ 1 := by
  induction a using WithZero.recZeroCoe with
  | zero => simp
  | coe m =>
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at ha
    rw [← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_le_coe]
    rw [← ofAdd_toAdd m, ← ofAdd_add, ← ofAdd_zero, Multiplicative.ofAdd_le]
    rw [← ofAdd_toAdd m, ← ofAdd_zero, Multiplicative.ofAdd_lt] at ha
    omega

theorem mem_span_piO_of_lt {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (y : intL L)
    (hy : Valued.v (y : L) < 1) : y ∈ Ideal.span {piO h} := by
  have hϖ : ϖ ≠ 0 := by
    intro h0
    have := h.2.2.2.1
    rw [h0, map_zero] at this
    exact WithZero.zero_ne_coe this
  have hc : (y : L) / ϖ ∈ intL L := by
    change Valued.v ((y : L) / ϖ) ≤ 1
    rw [map_div₀, h.2.2.2.1, div_eq_mul_inv, ← WithZero.coe_inv, ← ofAdd_neg, neg_neg]
    exact mul_ofAdd_one_le_of_lt_one hy
  rw [Ideal.mem_span_singleton']
  exact ⟨⟨_, hc⟩, Subtype.ext (by simp [div_mul_cancel₀ _ hϖ])⟩

theorem isUnit_of_v_eq_one (y : intL L) (hy : Valued.v (y : L) = 1) : IsUnit y := by
  have hy0 : (y : L) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hy; exact zero_ne_one hy
  have hinv : (y : L)⁻¹ ∈ intL L := by
    change Valued.v ((y : L)⁻¹) ≤ 1
    rw [map_inv₀, hy, inv_one]
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (by simp [hy0])⟩

theorem span_piO_isMaximal {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) :
    (Ideal.span {piO h}).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h1 => ?_, fun J y _ hy hyJ => ?_⟩
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
    have hv := congrArg (fun t : intL L => Valued.v (t : L)) hc
    simp only [Subring.coe_mul, coe_piO, map_mul, h.2.2.2.1, OneMemClass.coe_one, map_one] at hv
    have hc1 : Valued.v (c : L) ≤ 1 := c.2
    have hlt : Valued.v (c : L) * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 :=
      calc Valued.v (c : L) * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
          ≤ 1 * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by gcongr
        _ < 1 := by
          rw [one_mul]
          exact_mod_cast (WithZero.coe_lt_coe.2 (by decide : (Multiplicative.ofAdd (-1 : ℤ)) < 1))
    exact absurd hv hlt.ne
  · have hv : Valued.v (y : L) = 1 := by
      rcases lt_or_eq_of_le (show Valued.v (y : L) ≤ 1 from y.2) with hl | he
      · exact absurd (mem_span_piO_of_lt h y hl) hy
      · exact he
    rw [Ideal.eq_top_of_isUnit_mem J hyJ (isUnit_of_v_eq_one y hv)]
    trivial

theorem finite_quot_span_piO {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) :
    Finite (intL L ⧸ Ideal.span {piO h}) := by
  let V := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hc := h.2.2.2.2.2.2
  have hq := h.2.2.2.2.2.1
  have hfin0 := Nat.finite_of_card_ne_zero (hc.trans_ne (by positivity))
  haveI : Finite (V ⧸ IsLocalRing.maximalIdeal V) := hfin0
  let f : V →+* intL L :=
    { toFun := fun y => ⟨(y : L), (Valuation.mem_valuationSubring_iff _ _).1 y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hker : ∀ y ∈ IsLocalRing.maximalIdeal V, (Ideal.Quotient.mk (Ideal.span {piO h})).comp f y = 0 := by
    intro y hy
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    by_contra hn
    have hv : Valued.v (y : L) = 1 := by
      rcases lt_or_eq_of_le (show Valued.v (y : L) ≤ 1 from (f y).2) with hl | he
      · exact absurd (mem_span_piO_of_lt h (f y) hl) hn
      · exact he
    apply (IsLocalRing.mem_maximalIdeal _).1 hy
    have hy0 : (y : L) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
    have hinv : (y : L)⁻¹ ∈ V := by
      rw [Valuation.mem_valuationSubring_iff, map_inv₀, hv, inv_one]
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (show (y : L) * (y : L)⁻¹ = 1 from mul_inv_cancel₀ hy0)⟩
  let g := Ideal.Quotient.lift (IsLocalRing.maximalIdeal V) ((Ideal.Quotient.mk (Ideal.span {piO h})).comp f) hker
  refine Finite.of_surjective g fun a => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨Ideal.Quotient.mk _ ⟨(y : L), (Valuation.mem_valuationSubring_iff _ _).2 y.2⟩, ?_⟩
  rfl

theorem isReduced_adjoinRoot_of_separable {k : Type} [Field k] {f : k[X]} (hf : f.Separable) :
    IsReduced (AdjoinRoot f) := by
  first
  | exact @_root_.GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable
  | exact _root_.GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable
  | (apply _root_.GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable <;> assumption)
  | (intros; apply _root_.GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable ..)

theorem exists_mul_conj_sub_mem_piPow_one : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)),
    P.1.Separable → ∀ x : (GlobalTheory.UTr.Alg P)ˣ, x ∈ GlobalTheory.UTr.plus P → ∃ u : (GlobalTheory.UTr.Alg P)ˣ,
      (x : GlobalTheory.UTr.Alg P) - (u : GlobalTheory.UTr.Alg P) * GlobalTheory.UTr.conj P u ∈ GlobalTheory.NormEq.piPow h P 1 := by
  intro L _ _ σ ϖ q h P hP x hx
  classical
  let I0 : Ideal (intL L) := Ideal.span {piO h}
  haveI : I0.IsMaximal := span_piO_isMaximal h
  letI : Field (intL L ⧸ I0) := Ideal.Quotient.field I0
  haveI : Finite (intL L ⧸ I0) := finite_quot_span_piO h
  let J := piPow h P 1
  have hJ : J = (Ideal.map (AdjoinRoot.of P.1) I0 : Ideal (GlobalTheory.UTr.Alg P)) := by
    change Ideal.span {algebraMap (intL L) (GlobalTheory.UTr.Alg P) (piO h) ^ 1} =
      Ideal.map (AdjoinRoot.of P.1) (Ideal.span {piO h})
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    exact pow_one _
  let e1 : (GlobalTheory.UTr.Alg P ⧸ J) ≃+* (GlobalTheory.UTr.Alg P ⧸ (Ideal.map (AdjoinRoot.of P.1) I0 : Ideal (GlobalTheory.UTr.Alg P))) :=
    Ideal.quotEquivOfEq hJ
  let e2 : (GlobalTheory.UTr.Alg P ⧸ (Ideal.map (AdjoinRoot.of P.1) I0 : Ideal (GlobalTheory.UTr.Alg P))) ≃+*
      AdjoinRoot (P.1.map (Ideal.Quotient.mk I0)) :=
    AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot I0 P.1
  let e := e1.trans e2
  haveI : IsReduced (AdjoinRoot (P.1.map (Ideal.Quotient.mk I0))) :=
    isReduced_adjoinRoot_of_separable (hP.map)
  haveI : IsReduced (GlobalTheory.UTr.Alg P ⧸ J) := isReduced_of_injective e.toRingHom e.injective
  haveI : Module.Finite (intL L ⧸ I0) (AdjoinRoot (P.1.map (Ideal.Quotient.mk I0))) :=
    (AdjoinRoot.powerBasis' (P.2.1.map (Ideal.Quotient.mk I0))).finite
  haveI : Finite (AdjoinRoot (P.1.map (Ideal.Quotient.mk I0))) := Module.finite_of_finite (intL L ⧸ I0)
  haveI : Finite (GlobalTheory.UTr.Alg P ⧸ J) := Finite.of_equiv _ e.symm.toEquiv

  have hsig : ∀ b, sigO σ h.2.1 (sigO σ h.2.1 b) = b := fun b => Subtype.ext (h.1 b)
  have hsp : sigO σ h.2.1 (piO h) = piO h := Subtype.ext h.2.2.1
  have hle : J ≤ J.comap (GlobalTheory.UTr.conj P) := Ideal.span_le.2 (Set.singleton_subset_iff.2 (by
    change GlobalTheory.UTr.conj P _ ∈ J
    rw [map_pow, GlobalTheory.UTr.conj_algebraMap, hsp]
    exact Ideal.subset_span rfl))
  let τ := Ideal.quotientMap J (GlobalTheory.UTr.conj P) hle
  have hτ' : ∀ y, τ (Ideal.Quotient.mk J y) = Ideal.Quotient.mk J (GlobalTheory.UTr.conj P y) :=
    fun y => Ideal.quotientMap_mk
  have hτ : ∀ a, τ (τ a) = a := fun a => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hτ', hτ', GlobalTheory.UTr.conj_conj P hsig]

  obtain ⟨x0, hx0, hv⟩ := h.2.2.2.2.1
  let d : intL L := sigO σ h.2.1 ⟨x0, hx0⟩ - ⟨x0, hx0⟩
  have hd : IsUnit d := isUnit_of_v_eq_one d (by simpa [d] using hv)
  let b : GlobalTheory.UTr.Alg P ⧸ J := Ideal.Quotient.mk J (algebraMap (intL L) _ ⟨x0, hx0⟩)
  have hb : IsUnit (τ b - b) := by
    have : τ b - b = Ideal.Quotient.mk J (algebraMap (intL L) (GlobalTheory.UTr.Alg P) d) := by
      simp only [b, hτ', GlobalTheory.UTr.conj_algebraMap, d, map_sub]
    rw [this]
    exact (hd.map _).map _
  have hxu : IsUnit (Ideal.Quotient.mk J (x : GlobalTheory.UTr.Alg P)) := x.isUnit.map _
  have hxτ : τ (Ideal.Quotient.mk J (x : GlobalTheory.UTr.Alg P)) = Ideal.Quotient.mk J (x : GlobalTheory.UTr.Alg P) := by
    rw [hτ', GlobalTheory.UTr.mem_plus.1 hx]
  obtain ⟨zb, hzb, hzz⟩ := exists_mul_invol_eq_of_fixed_unit τ hτ hb hxu hxτ
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective zb
  obtain ⟨wb, hw⟩ := hzb.exists_right_inv
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective wb
  have hzw : IsUnit (z * w) := isUnit_of_sub_one_mem h P le_rfl (by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hw, map_one, sub_self])
  have hz : IsUnit z := isUnit_of_mul_isUnit_left hzw
  refine ⟨hz.unit, ?_⟩
  rw [IsUnit.unit_spec]
  change _ ∈ J
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hτ', hzz, sub_self]

end GlobalTheory.NormEq
