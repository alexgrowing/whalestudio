import Mathlib
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import Formalism.PeriodIntegrals.BallQuotLen
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EfRankSum

namespace PI.UnitaryGroupMassFormula.BallQuotLen

open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing

section Gen

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {A : Type*} [CommRing A] [Algebra O A] {ϖ : O}

private theorem enat_map_natCast_int_eq_top_iff (a : ℕ∞) : a.map (Nat.cast : ℕ → ℤ) = ⊤ ↔ a = ⊤ := by
  cases a <;> simp

theorem eq_zero_of_ord_top [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) {x : A}
    (hx : ∀ ζ : Pts O A, ord ϖ ζ x = ⊤) : x = 0 := by
  obtain ⟨n, hn⟩ := h.denom x
  have hy : (⟨ϖ ^ n • x, hn⟩ : ↥(As O A)) = 0 := by
    refine eq_zero_of_localization _ (fun J hJ => ?_)
    have hv : vL (⟨J, hJ⟩ : Pts O A) ⟨ϖ ^ n • x, hn⟩ = ⊤ := by
      have := hx ⟨J, hJ⟩
      rw [ord_eq (ζ := (⟨J, hJ⟩ : Pts O A)) h hn, ordAt, WithTop.add_eq_top] at this
      rcases this with h1 | h1
      · exact (enat_map_natCast_int_eq_top_iff _).mp h1
      · exact absurd h1 WithTop.coe_ne_top
    exact (vL_eq_top_iff (ζ := (⟨J, hJ⟩ : Pts O A)) _).mp hv
  have h0 : ϖ ^ n • x = 0 := congrArg Subtype.val hy
  rw [Algebra.smul_def, map_pow] at h0
  exact (h.isUnit.pow n).mul_right_eq_zero.mp h0

theorem isUnit_of_ord_ne_top (K : Type*) [Field K] [Algebra K A] [FiniteDimensional K A]
    [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) {x : A} (hx : ∀ ζ : Pts O A, ord ϖ ζ x ≠ ⊤) :
    IsUnit x := by
  have hnz : x ∈ nonZeroDivisors A := by
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    refine eq_zero_of_ord_top h (fun ζ => ?_)
    have := ord_mul (ζ := ζ) h x y
    rw [mul_comm x y, hy, ord_zero (ζ := ζ) h] at this
    rcases WithTop.add_eq_top.mp this.symm with h1 | h1
    · exact absurd h1 (hx ζ)
    · exact h1
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  exact IsArtinianRing.isUnit_of_mem_nonZeroDivisors hnz

theorem exists_param [Finite (Pts O A)] (ζ₀ : Pts O A) [IsDVRAt ζ₀] :
    ∃ t : ↥(As O A), vL ζ₀ t = 1 ∧ ∀ ζ : Pts O A, ζ ≠ ζ₀ → t ∉ ζ.asIdeal := by
  classical
  haveI := Fintype.ofFinite (Pts O A)
  haveI : IsDomain (Loc ζ₀) := IsDVRAt.isDomain
  haveI : IsDiscreteValuationRing (Loc ζ₀) := IsDVRAt.isDVR
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Loc ζ₀)
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.mk'_surjective ζ₀.asIdeal.primeCompl π
  have hva : vL ζ₀ a = 1 := by
    rw [vL_eq_addVal]
    have e1 : algebraMap _ (Loc ζ₀) a = π * algebraMap _ (Loc ζ₀) (s : ↥(As O A)) := by
      rw [← has, IsLocalization.mk'_spec]
    obtain ⟨u, hu⟩ := IsLocalization.map_units (Loc ζ₀) s
    rw [e1, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_uniformizer hπ, ← hu,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, add_zero]
  have h1 : ∀ x ∈ ζ₀.asIdeal, 1 ≤ vL ζ₀ x := by
    intro x hx
    rw [ENat.one_le_iff_ne_zero]
    intro h0
    exact ((vL_eq_zero_iff (ζ := ζ₀) x).mp h0) hx
  have h2 : ∀ x ∈ ζ₀.asIdeal ^ 2, 2 ≤ vL ζ₀ x := by
    intro x hx
    rw [sq] at hx
    refine Submodule.mul_induction_on hx (fun p hp q hq => ?_) (fun x y hx hy => ?_)
    · rw [vL_mul]
      calc (2 : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ _ := add_le_add (h1 p hp) (h1 q hq)
    · exact le_trans (le_min hx hy) (vL_add (ζ := ζ₀) x y)
  have hcop : ζ₀.asIdeal ^ 2 ⊔ ⨅ ζ ∈ (Finset.univ.filter (· ≠ ζ₀)), ζ.asIdeal = ⊤ := by
    refine Ideal.sup_iInf_eq_top (fun ζ hζ => ?_)
    have hne : ζ₀.asIdeal ≠ ζ.asIdeal := by
      intro heq
      exact (Finset.mem_filter.mp hζ).2 (MaximalSpectrum.ext heq).symm
    have hc : IsCoprime ζ₀.asIdeal ζ.asIdeal :=
      Ideal.isCoprime_iff_sup_eq.mpr (ζ₀.isMaximal.coprime_of_ne ζ.isMaximal hne)
    exact Ideal.isCoprime_iff_sup_eq.mp (hc.pow_left (m := 2))
  have hone : (1 : ↥(As O A)) ∈ ζ₀.asIdeal ^ 2 ⊔ ⨅ ζ ∈ (Finset.univ.filter (· ≠ ζ₀)), ζ.asIdeal := by
    rw [hcop]
    exact Submodule.mem_top
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp hone
  have hjmem : ∀ ζ : Pts O A, ζ ≠ ζ₀ → j ∈ ζ.asIdeal := by
    intro ζ hz
    simp only [Submodule.mem_iInf] at hj
    exact hj ζ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩)
  refine ⟨a * j + i, ?_, ?_⟩
  · have hj' : j = 1 - i := eq_sub_of_add_eq' hij
    have ht : a * j + i = a + i * (1 - a) := by rw [hj']; ring
    have hr : 2 ≤ vL ζ₀ (i * (1 - a)) := by
      rw [vL_mul]
      exact le_trans (h2 i hi) le_self_add
    have hlt : vL ζ₀ a < vL ζ₀ (i * (1 - a)) := by
      rw [hva]
      exact lt_of_lt_of_le (by norm_num) hr
    rw [ht, vL_eq_addVal, map_add, AddValuation.map_add_of_distinct_val, ← vL_eq_addVal,
      ← vL_eq_addVal, min_eq_left hlt.le, hva]
    rw [← vL_eq_addVal, ← vL_eq_addVal]
    exact hlt.ne
  · intro ζ hz ht
    have hi' : i ∈ ζ.asIdeal := by
      have := ζ.asIdeal.sub_mem ht (ζ.asIdeal.mul_mem_left a (hjmem ζ hz))
      simpa using this
    have : (1 : ↥(As O A)) ∈ ζ.asIdeal := by
      rw [← hij]
      exact ζ.asIdeal.add_mem hi' (hjmem ζ hz)
    exact ζ.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr this)

open Classical in

theorem exists_unit_param (K : Type*) [Field K] [Algebra K A] [FiniteDimensional K A]
    [Finite (Pts O A)] [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (ζ₀ : Pts O A) :
    ∃ t : Aˣ, ∀ ζ : Pts O A, ord ϖ ζ (t : A) = (((if ζ = ζ₀ then 1 else 0 : ℤ)) : WithTop ℤ) := by
  obtain ⟨t, ht1, ht2⟩ := exists_param ζ₀
  have hord : ∀ ζ : Pts O A, ord ϖ ζ (t : A) = (((if ζ = ζ₀ then 1 else 0 : ℤ)) : WithTop ℤ) := by
    intro ζ
    rw [ord_of_mem (ζ := ζ) h t.2]
    split_ifs with hz
    · subst hz
      rw [show (⟨(t : A), t.2⟩ : ↥(As O A)) = t from rfl, ht1]
      rfl
    · rw [show (⟨(t : A), t.2⟩ : ↥(As O A)) = t from rfl, (vL_eq_zero_iff (ζ := ζ) t).mpr (ht2 ζ hz)]
      rfl
  have hu : IsUnit (t : A) :=
    isUnit_of_ord_ne_top K h (fun ζ => by rw [hord]; exact WithTop.coe_ne_top)
  exact ⟨hu.unit, fun ζ => by rw [hu.unit_spec]; exact hord ζ⟩

private theorem ordZ_one (h : IsUnif A ϖ) (ζ : Pts O A) [IsDVRAt ζ] : ordZ ϖ ζ (1 : A) = 0 := by
  have := coe_ordZ (ζ := ζ) h (one_mem (nonZeroDivisors A))
  rw [ord_one (ζ := ζ) h] at this
  exact_mod_cast this

private theorem ordZ_units_mul (h : IsUnif A ϖ) (ζ : Pts O A) [IsDVRAt ζ] (v w : Aˣ) :
    ordZ ϖ ζ ((v : A) * w) = ordZ ϖ ζ v + ordZ ϖ ζ w := by
  have hv := coe_ordZ (ζ := ζ) h v.isUnit.mem_nonZeroDivisors
  have hw := coe_ordZ (ζ := ζ) h w.isUnit.mem_nonZeroDivisors
  have hvw := coe_ordZ (ζ := ζ) h (v * w).isUnit.mem_nonZeroDivisors
  rw [Units.val_mul, ord_mul (ζ := ζ) h, ← hv, ← hw] at hvw
  exact_mod_cast hvw

theorem exists_unit_ord (K : Type*) [Field K] [Algebra K A] [FiniteDimensional K A]
    [Finite (Pts O A)] [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (d : Pts O A → ℤ) :
    ∃ u : Aˣ, ∀ ζ : Pts O A, ord ϖ ζ (u : A) = ((d ζ : ℤ) : WithTop ℤ) := by
  classical
  haveI := Fintype.ofFinite (Pts O A)
  choose t ht using exists_unit_param K h
  let φ : Pts O A → Aˣ →* Multiplicative ℤ := fun ζ =>
    { toFun := fun v => Multiplicative.ofAdd (ordZ ϖ ζ (v : A))
      map_one' := by simp only [Units.val_one, ordZ_one h ζ]; rfl
      map_mul' := fun v w => by simp only [Units.val_mul, ordZ_units_mul h ζ v w]; rfl }
  refine ⟨∏ ζ', t ζ' ^ d ζ', fun ζ => ?_⟩
  have e2 : ∀ ζ', Multiplicative.toAdd (φ ζ (t ζ')) = if ζ = ζ' then 1 else 0 := by
    intro ζ'
    show ordZ ϖ ζ (t ζ' : A) = _
    have := coe_ordZ (ζ := ζ) h (t ζ').isUnit.mem_nonZeroDivisors
    rw [ht ζ' ζ] at this
    exact_mod_cast this
  have hz : ordZ ϖ ζ ((∏ ζ', t ζ' ^ d ζ' : Aˣ) : A) = d ζ := by
    have e1 : Multiplicative.toAdd (φ ζ (∏ ζ', t ζ' ^ d ζ')) =
        ordZ ϖ ζ ((∏ ζ', t ζ' ^ d ζ' : Aˣ) : A) := rfl
    rw [← e1, map_prod, toAdd_prod]
    simp only [map_zpow, toAdd_zpow, e2, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← coe_ordZ (ζ := ζ) h (Units.isUnit _).mem_nonZeroDivisors, hz]

theorem ord_sub_one_nonneg_iff (h : IsUnif A ϖ) (ζ : Pts O A) [IsDVRAt ζ] (x : ↥(As O A)) :
    0 ≤ ord ϖ ζ (x : A) + ((-1 : ℤ) : WithTop ℤ) ↔ x ∈ ζ.asIdeal := by
  rw [ord_of_mem (ζ := ζ) h x.2]
  have e := vL_eq_zero_iff (ζ := ζ) x
  rw [← not_not (a := x ∈ ζ.asIdeal), ← e]
  show 0 ≤ (vL ζ x).map (Nat.cast : ℕ → ℤ) + ((-1 : ℤ) : WithTop ℤ) ↔ ¬ vL ζ x = 0
  generalize vL ζ x = v
  induction v using ENat.recTopCoe with
  | top => simp
  | coe n =>
    simp only [ENat.map_coe, ← WithTop.coe_add, WithTop.coe_nonneg, Nat.cast_eq_zero]
    constructor <;> intro hh <;> omega

theorem length_quot_add {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {N P Q : Submodule R M} (h1 : N ≤ P) (h2 : P ≤ Q) :
    Module.length R (↥Q ⧸ N.comap Q.subtype) =
      Module.length R (↥P ⧸ N.comap P.subtype) + Module.length R (↥Q ⧸ P.comap Q.subtype) := by
  have hle1 : N.comap P.subtype ≤ (N.comap Q.subtype).comap (Submodule.inclusion h2) := by
    intro x hx
    simpa using hx
  have hle2 : N.comap Q.subtype ≤ (P.comap Q.subtype).comap LinearMap.id := by
    intro x hx
    exact h1 hx
  refine Module.length_eq_add_of_exact
    (Submodule.mapQ _ _ (Submodule.inclusion h2) hle1) (Submodule.mapQ _ _ LinearMap.id hle2) ?_ ?_ ?_
  · intro x y hxy
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    simp only [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at hxy ⊢
    simpa using hxy
  · intro y
    obtain ⟨q, rfl⟩ := Submodule.mkQ_surjective _ y
    exact ⟨Submodule.Quotient.mk q, by simp⟩
  · intro y
    obtain ⟨q, rfl⟩ := Submodule.mkQ_surjective _ y
    simp only [Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.id_apply, Set.mem_range,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro hq
      refine ⟨Submodule.Quotient.mk ⟨q, hq⟩, ?_⟩
      rw [Submodule.mapQ_apply]
      rfl
    · rintro ⟨x, hx⟩
      obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ x
      rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at hx
      have h3 := h1 hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
        Submodule.coe_inclusion] at h3
      have h4 := P.sub_mem p.2 h3
      simpa using h4

theorem length_zero_of_le {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {N P : Submodule R M} (h : P ≤ N) : Module.length R (↥P ⧸ N.comap P.subtype) = 0 := by
  rw [Module.length_eq_zero_iff]
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ b
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact h (a - b).2

set_option synthInstance.maxHeartbeats 400000 in

theorem length_residue (hfin : Module.Finite O ↥(As O A)) (ζ : Pts O A) :
    Module.length O (↥(As O A) ⧸ ζ.asIdeal) = (fdeg ζ : ℕ∞) := by
  classical
  haveI : ζ.asIdeal.IsMaximal := ζ.isMaximal
  haveI : Algebra.IsIntegral O ↥(As O A) := Algebra.IsIntegral.of_finite O _
  have hmax : (ζ.asIdeal.comap (algebraMap O ↥(As O A))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal ζ.asIdeal
  have hp : ζ.asIdeal.comap (algebraMap O ↥(As O A)) = IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal hmax
  haveI : ζ.asIdeal.LiesOver (IsLocalRing.maximalIdeal O) := ⟨hp.symm⟩
  have hf : fdeg ζ = Module.finrank (O ⧸ IsLocalRing.maximalIdeal O) (↥(As O A) ⧸ ζ.asIdeal) := by
    rw [fdeg_eq_inertiaDeg, ← Ideal.inertiaDeg'_eq_inertiaDeg (IsLocalRing.maximalIdeal O) ζ.asIdeal,
      Ideal.inertiaDeg_algebraMap]
  letI : Field (O ⧸ IsLocalRing.maximalIdeal O) := Ideal.Quotient.field _
  haveI : Module.Finite O (↥(As O A) ⧸ ζ.asIdeal) :=
    Module.Finite.of_surjective ((ζ.asIdeal.restrictScalars O).mkQ) (Submodule.mkQ_surjective _)
  haveI : Module.Finite (O ⧸ IsLocalRing.maximalIdeal O) (↥(As O A) ⧸ ζ.asIdeal) :=
    Module.Finite.of_restrictScalars_finite O _ _
  let b := Module.finBasis (O ⧸ IsLocalRing.maximalIdeal O) (↥(As O A) ⧸ ζ.asIdeal)
  let eqv := b.equivFun.restrictScalars O
  have h1 : Module.length O (O ⧸ IsLocalRing.maximalIdeal O) = 1 :=
    Module.length_eq_one_iff.mpr (isSimpleModule_iff_isCoatom.mpr
      (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal O)))
  rw [hf, eqv.length_eq, Module.length_pi, h1, mul_one, ENat.card_eq_coe_fintype_card, Fintype.card_fin]

variable {V : Type*} [AddCommGroup V] [Module A V] [Module O V] [IsScalarTower O A V] {e : V}

theorem ballO_mono [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e)
    {c c' : Pts O A → ℤ} (hc : ∀ ζ, c ζ ≤ c' ζ) : ballO ϖ e c ≤ ballO ϖ e c' := fun v hv => ball_mono h he hc hv

open Classical in

theorem length_step (K : Type*) [Field K] [Algebra K A] [FiniteDimensional K A]
    [Finite (Pts O A)] [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (hfin : Module.Finite O ↥(As O A))
    (he : IsGen A e) (c d : Pts O A → ℤ) (ζ₀ : Pts O A)
    (hd : ∀ ζ, d ζ = c ζ + if ζ = ζ₀ then 1 else 0) :
    Module.length O (↥(ballO ϖ e d) ⧸ (ballO ϖ e c).comap (ballO ϖ e d).subtype) = fdeg ζ₀ := by
  classical
  obtain ⟨w, hw⟩ := exists_unit_ord K h (fun ζ => -d ζ)
  have hwi : ∀ ζ, ord ϖ ζ ((w⁻¹ : Aˣ) : A) = ((d ζ : ℤ) : WithTop ℤ) := by
    intro ζ
    have e := ord_units_add_inv (ζ := ζ) h w
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp
      (ord_ne_top (ζ := ζ) h (w⁻¹).isUnit.mem_nonZeroDivisors)
    rw [← hk, hw ζ] at e
    rw [← hk]
    have e' : -d ζ + k = 0 := by exact_mod_cast e
    congr 1
    omega
  have hov : ∀ (c' : Pts O A → ℤ) (b : ↥(As O A)) (ζ : Pts O A),
      ordV ϖ ζ e c' (((b : A) * w) • e) = ord ϖ ζ (b : A) + ((c' ζ - d ζ : ℤ) : WithTop ℤ) := by
    intro c' b ζ
    simp only [ordV]
    rw [coord_smul_gen he, ord_mul (ζ := ζ) h, hw ζ, add_assoc, ← WithTop.coe_add]
    rw [show -d ζ + c' ζ = c' ζ - d ζ by ring]
  have hmemd : ∀ b : ↥(As O A), ((b : A) * w) • e ∈ ballO ϖ e d := by
    intro b
    show ((b : A) * w) • e ∈ ball ϖ e d
    rw [mem_ball_iff (h := h) (he := he)]
    intro ζ
    rw [hov, sub_self, WithTop.coe_zero, add_zero]
    exact ord_nonneg (ζ := ζ) h b.2
  let f : ↥(As O A) →ₗ[O] ↥(ballO ϖ e d) :=
    { toFun := fun b => ⟨((b : A) * w) • e, hmemd b⟩
      map_add' := fun x y => by
        apply Subtype.ext
        simp only [Subalgebra.coe_add, add_mul, add_smul, Submodule.coe_add]
      map_smul' := fun r x => by
        apply Subtype.ext
        simp only [Subalgebra.coe_smul, RingHom.id_apply, Submodule.coe_smul, smul_mul_assoc,
          smul_assoc] }
  let G := ((ballO ϖ e c).comap (ballO ϖ e d).subtype).mkQ ∘ₗ f
  have hsurj : Function.Surjective G := by
    intro y
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ y
    have hv : ∀ ζ : Pts O A, 0 ≤ ordV ϖ ζ e d (v : V) := (mem_ball_iff (c := d) (h := h) (he := he) (v := (v : V))).mp v.2
    have hb : (coord e (v : V) : A) * ((w⁻¹ : Aˣ) : A) ∈ As O A := by
      rw [mem_As_iff h]
      intro ζ
      rw [ord_mul (ζ := ζ) h, hwi ζ]
      exact hv ζ
    refine ⟨⟨_, hb⟩, ?_⟩
    show Submodule.mkQ _ (f ⟨_, hb⟩) = Submodule.mkQ _ v
    congr 1
    apply Subtype.ext
    show ((coord e (v : V) : A) * ((w⁻¹ : Aˣ) : A) * w) • e = v
    rw [mul_assoc, Units.inv_mul, mul_one, coord_smul_self he]
  have hker : LinearMap.ker G = ζ₀.asIdeal.restrictScalars O := by
    ext b
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem]
    show Submodule.mkQ _ (f b) = 0 ↔ b ∈ ζ₀.asIdeal
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply]
    show ((b : A) * w) • e ∈ ball ϖ e c ↔ b ∈ ζ₀.asIdeal
    rw [mem_ball_iff (h := h) (he := he)]
    constructor
    · intro H
      have := H ζ₀
      rw [hov, hd ζ₀, if_pos rfl, show c ζ₀ - (c ζ₀ + 1) = (-1 : ℤ) by ring] at this
      exact (ord_sub_one_nonneg_iff h ζ₀ b).mp this
    · intro hb ζ
      rw [hov, hd ζ]
      by_cases hz : ζ = ζ₀
      · subst hz
        rw [if_pos rfl, show c ζ - (c ζ + 1) = (-1 : ℤ) by ring]
        exact (ord_sub_one_nonneg_iff h ζ b).mpr hb
      · rw [if_neg hz, show c ζ - (c ζ + 0) = (0 : ℤ) by ring, WithTop.coe_zero, add_zero]
        exact ord_nonneg (ζ := ζ) h b.2
  rw [← (G.quotKerEquivOfSurjective hsurj).length_eq,
    (Submodule.quotEquivOfEq _ _ hker).length_eq,
    (Submodule.Quotient.restrictScalarsEquiv O ζ₀.asIdeal).length_eq]
  exact length_residue hfin ζ₀

theorem length_ball_quotient_eq_sum_mul_fdeg (K : Type*) [Field K] [Algebra K A] [FiniteDimensional K A]
    [Fintype (Pts O A)] [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ)
    (hfin : Module.Finite O ↥(As O A)) (he : IsGen A e) :
    ∀ (n : ℕ) (c : Pts O A → ℤ) (m : Pts O A → ℕ), ∑ ζ, m ζ = n →
      Module.length O (↥(ballO ϖ e (fun ζ => c ζ + m ζ)) ⧸
          (ballO ϖ e c).comap (ballO ϖ e (fun ζ => c ζ + m ζ)).subtype) =
        ((∑ ζ, m ζ * fdeg ζ : ℕ) : ℕ∞) := by
  classical
  intro n
  induction n with
  | zero =>
    intro c m hm
    have hm0 : ∀ ζ, m ζ = 0 := fun ζ => (Finset.sum_eq_zero_iff.mp hm) ζ (Finset.mem_univ _)
    simp only [hm0, Nat.cast_zero, add_zero, zero_mul, Finset.sum_const_zero]
    exact length_zero_of_le (ballO_mono h he (fun ζ => by simp [hm0 ζ]))
  | succ n ih =>
    intro c m hm
    obtain ⟨ζ₀, hζ₀⟩ : ∃ ζ₀, m ζ₀ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      simp [hcon] at hm
    let m' : Pts O A → ℕ := fun ζ => if ζ = ζ₀ then m ζ - 1 else m ζ
    have hmm : ∀ ζ, m ζ = m' ζ + if ζ = ζ₀ then 1 else 0 := by
      intro ζ
      by_cases hz : ζ = ζ₀
      · subst hz
        show m ζ = (if ζ = ζ then m ζ - 1 else m ζ) + if ζ = ζ then 1 else 0
        rw [if_pos rfl, if_pos rfl]
        omega
      · show m ζ = (if ζ = ζ₀ then m ζ - 1 else m ζ) + if ζ = ζ₀ then 1 else 0
        rw [if_neg hz, if_neg hz, add_zero]
    have hsum : ∑ ζ, m ζ = ∑ ζ, m' ζ + 1 := by
      rw [Finset.sum_congr rfl (fun ζ _ => hmm ζ), Finset.sum_add_distrib]
      simp
    have hm' : ∑ ζ, m' ζ = n := by omega
    have hle1 : ballO ϖ e c ≤ ballO ϖ e (fun ζ => c ζ + (m' ζ : ℤ)) :=
      ballO_mono h he (fun ζ => le_add_of_nonneg_right (Nat.cast_nonneg _))
    have hle2 : ballO ϖ e (fun ζ => c ζ + (m' ζ : ℤ)) ≤ ballO ϖ e (fun ζ => c ζ + (m ζ : ℤ)) :=
      ballO_mono h he (fun ζ => show c ζ + (m' ζ : ℤ) ≤ c ζ + (m ζ : ℤ) by
        have h5 : (m' ζ : ℤ) ≤ (m ζ : ℤ) :=
          Nat.cast_le.mpr (le_trans (Nat.le_add_right _ _) (hmm ζ).symm.le)
        linarith)
    have hd : ∀ ζ, (fun ζ => c ζ + (m ζ : ℤ)) ζ =
        (fun ζ => c ζ + (m' ζ : ℤ)) ζ + if ζ = ζ₀ then 1 else 0 := by
      intro ζ
      beta_reduce
      rw [hmm ζ]
      split_ifs <;> push_cast <;> ring
    have hs : ∑ ζ, m ζ * fdeg ζ = ∑ ζ, m' ζ * fdeg ζ + fdeg ζ₀ := by
      rw [Finset.sum_congr rfl (fun ζ _ => by rw [hmm ζ, add_mul]), Finset.sum_add_distrib]
      congr 1
      simp [ite_mul]
    rw [length_quot_add hle1 hle2, ih c m' hm', length_step K h hfin he _ _ ζ₀ hd, hs, Nat.cast_add]

end Gen

theorem ballQuotLen_main : PI.BallQuotLen := by
  intro O _ _ _ K _ _ _ A _ _ _ _ _ _ ϖ hϖ hfin _ V _ _ _ _ _ _ e he c m
  classical
  haveI : Module.Finite O ↥(As O A) := hfin
  haveI : Finite (Pts O A) := PI.UnitaryGroupMassFormula.EfRankSum.finite_pts O A
  letI : Fintype (Pts O A) := Fintype.ofFinite _
  have h : IsUnif A ϖ := by
    refine ⟨hϖ, ?_, ?_⟩
    · rw [IsScalarTower.algebraMap_apply O K A]
      refine IsUnit.map _ (isUnit_iff_ne_zero.mpr ?_)
      intro h0
      exact hϖ.ne_zero ((IsFractionRing.injective O K) (h0.trans (map_zero _).symm))
    · intro x
      have halg : IsAlgebraic O x :=
        (IsFractionRing.isAlgebraic_iff O K A).mpr (Algebra.IsAlgebraic.isAlgebraic x)
      obtain ⟨y, hy0, hyx⟩ := halg.exists_integral_multiple
      obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
      refine ⟨k, ?_⟩
      have e1 : ϖ ^ k • x = ((u⁻¹ : Oˣ) : O) • (((u : O) * ϖ ^ k) • x) := by
        rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul]
      rw [e1]
      exact IsIntegral.smul _ hyx
  rw [finsum_eq_sum_of_fintype]
  exact length_ball_quotient_eq_sum_mul_fdeg K h hfin he (∑ ζ, m ζ) c m rfl

end PI.UnitaryGroupMassFormula.BallQuotLen
