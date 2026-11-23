import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.PlaceCompletion

open scoped WithZero

section Val

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']

theorem valV_algebraMap_le_one (v : V) : valV V (algebraMap V K' v) ≤ 1 := by
  unfold valV
  apply HeightOneSpectrum.valuation_le_one

theorem valV_algebraMap_lt_one_iff (v : V) :
    valV V (algebraMap V K' v) < 1 ↔ v ∈ IsLocalRing.maximalIdeal V := by
  unfold valV
  exact HeightOneSpectrum.valuation_lt_one_iff_mem _ v

theorem valV_algebraMap_of_isUnit {v : V} (hv : IsUnit v) : valV V (algebraMap V K' v) = 1 := by
  refine le_antisymm (valV_algebraMap_le_one v) (not_lt.1 fun hlt => ?_)
  have hm := (valV_algebraMap_lt_one_iff v).1 hlt
  exact (IsLocalRing.mem_maximalIdeal v).1 hm hv

theorem valV_algebraMap_of_irreducible {v : V} (hv : Irreducible v) :
    valV V (algebraMap V K' v) = WithZero.exp (-1 : ℤ) := by
  have hspan := (IsDiscreteValuationRing.irreducible_iff_uniformizer v).1 hv
  unfold valV
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (IsDiscreteValuationRing.maximalIdeal V).intValuation_singleton hv.ne_zero hspan

theorem exists_algebraMap_eq_of_valV_le_one {x : K'} (hx : valV V x ≤ 1) :
    ∃ v : V, algebraMap V K' v = x := by
  have honly : ∀ w : HeightOneSpectrum V, w = IsDiscreteValuationRing.maximalIdeal V := fun w =>
    HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal w.isMaximal)
  unfold valV at hx
  obtain ⟨v, hv⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := V) (K := K') x
    (fun w => by rw [honly w]; exact hx)
  exact ⟨v, hv⟩

end Val

section Place

variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] (la : HeightOneSpectrum R)

theorem mem_atPrime_iff (x : K) : x ∈ la.valuationSubringAtPrime K ↔ la.valuation K x ≤ 1 := by
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact Iff.rfl

theorem isUnit_atPrime_iff (x : la.valuationSubringAtPrime K) :
    IsUnit x ↔ la.valuation K (x : K) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 := (mem_atPrime_iff la ((u : la.valuationSubringAtPrime K) : K)).1 (u : la.valuationSubringAtPrime K).2
    have h2 := (mem_atPrime_iff la (((u⁻¹ : (la.valuationSubringAtPrime K)ˣ) : la.valuationSubringAtPrime K) : K)).1
      ((u⁻¹ : (la.valuationSubringAtPrime K)ˣ) : la.valuationSubringAtPrime K).2
    have hprod : la.valuation K ((u : la.valuationSubringAtPrime K) : K) *
        la.valuation K (((u⁻¹ : (la.valuationSubringAtPrime K)ˣ) : la.valuationSubringAtPrime K) : K) = 1 := by
      rw [← map_mul]
      have : ((u : la.valuationSubringAtPrime K) : K) *
          (((u⁻¹ : (la.valuationSubringAtPrime K)ˣ) : la.valuationSubringAtPrime K) : K) = 1 := by
        exact congrArg Subtype.val u.mul_inv
      rw [this, map_one]
    refine le_antisymm h1 ?_
    calc (1 : ℤᵐ⁰) = _ := hprod.symm
      _ ≤ la.valuation K ((u : la.valuationSubringAtPrime K) : K) * 1 := by gcongr
      _ = _ := mul_one _
  · intro h
    have hx0 : (x : K) ≠ 0 := fun h0 => by rw [h0, map_zero] at h; exact zero_ne_one h
    have hinv : (x : K)⁻¹ ∈ la.valuationSubringAtPrime K :=
      (mem_atPrime_iff la _).2 (by rw [map_inv₀, h, inv_one])
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

theorem valuation_of_irreducible [IsDiscreteValuationRing (la.valuationSubringAtPrime K)]
    {π : la.valuationSubringAtPrime K} (hπ : Irreducible π) :
    la.valuation K (π : K) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨ϖ, hϖ⟩ := la.valuation_exists_uniformizer K
  have hle : ϖ ∈ la.valuationSubringAtPrime K := (mem_atPrime_iff la ϖ).2 (by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)
  have hnu : ¬ IsUnit (⟨ϖ, hle⟩ : la.valuationSubringAtPrime K) := fun hu => by
    have := (isUnit_atPrime_iff la _).1 hu
    rw [show ((⟨ϖ, hle⟩ : la.valuationSubringAtPrime K) : K) = ϖ from rfl, hϖ,
      WithZero.exp_eq_one] at this
    norm_num at this
  have hm : (⟨ϖ, hle⟩ : la.valuationSubringAtPrime K) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.mem_maximalIdeal _).2 hnu
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.mem_span_singleton'] at hm
  obtain ⟨a, ha⟩ := hm
  have hprod : la.valuation K (a : K) * la.valuation K (π : K) = WithZero.exp (-1 : ℤ) := by
    rw [← map_mul, ← hϖ]
    exact congrArg _ (congrArg Subtype.val ha)
  have hp0 : la.valuation K (π : K) ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hprod; exact WithZero.exp_ne_zero hprod.symm
  have hq0 : la.valuation K (a : K) ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hprod; exact WithZero.exp_ne_zero hprod.symm
  have hp1 : la.valuation K (π : K) < 1 := lt_of_le_of_ne ((mem_atPrime_iff la _).1 π.2)
    (fun h1 => hπ.not_isUnit ((isUnit_atPrime_iff la π).2 h1))
  have hq1 : la.valuation K (a : K) ≤ 1 := (mem_atPrime_iff la _).1 a.2
  have hlog := congrArg WithZero.log hprod
  rw [WithZero.log_mul hq0 hp0, WithZero.log_exp] at hlog
  have hlp : WithZero.log (la.valuation K (π : K)) < 0 := by
    rw [WithZero.log_lt_iff_lt_exp hp0, WithZero.exp_zero]; exact hp1
  have hlq : WithZero.log (la.valuation K (a : K)) ≤ 0 := by
    rw [WithZero.log_le_iff_le_exp hq0, WithZero.exp_zero]; exact hq1
  rw [← WithZero.exp_log hp0]
  congr 1
  omega

private theorem valV_algebraMap_eq_valuation {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K'] [Algebra V K'] [IsFractionRing V K'] [IsDiscreteValuationRing (la.valuationSubringAtPrime K)]
    (o : la.valuationSubringAtPrime K →+* V) {π : la.valuationSubringAtPrime K}
    (hπ : Irreducible π) (hoπ : Irreducible (o π)) (x : la.valuationSubringAtPrime K) :
    valV V (algebraMap V K' (o x)) = la.valuation K (x : K) := by
  by_cases hx : x = 0
  · subst hx
    simp
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  have hc : (((u : la.valuationSubringAtPrime K) * π ^ n : la.valuationSubringAtPrime K) : K) =
      ((u : la.valuationSubringAtPrime K) : K) * (π : K) ^ n := by
    rfl
  rw [hc]
  simp only [map_mul, map_pow]
  rw [valV_algebraMap_of_isUnit (u.isUnit.map o), valV_algebraMap_of_irreducible hoπ,
    (isUnit_atPrime_iff la _).1 u.isUnit, valuation_of_irreducible la hπ]

private theorem valV_ringHom_eq_valuation {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K'] [Algebra V K'] [IsFractionRing V K'] [IsDiscreteValuationRing (la.valuationSubringAtPrime K)]
    (j : K →+* K') (o : la.valuationSubringAtPrime K →+* V)
    (ho : ∀ x, algebraMap V K' (o x) = j x) {π : la.valuationSubringAtPrime K}
    (hπ : Irreducible π) (hoπ : Irreducible (o π)) (a : K) :
    valV V (j a) = la.valuation K a := by
  rcases ValuationSubring.mem_or_inv_mem (la.valuationSubringAtPrime K) a with h | h
  · have key := valV_algebraMap_eq_valuation la (K' := K') o hπ hoπ ⟨a, h⟩
    rw [ho] at key
    exact key
  · have key := valV_algebraMap_eq_valuation la (K' := K') o hπ hoπ ⟨a⁻¹, h⟩
    rw [ho] at key
    change valV V (j a⁻¹) = la.valuation K a⁻¹ at key
    rw [map_inv₀, map_inv₀, map_inv₀] at key
    exact inv_injective key

variable {la} {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']

theorem overLa_one_of_irreducible [IsDiscreteValuationRing (la.valuationSubringAtPrime K)]
    (j : K →+* K') (o : la.valuationSubringAtPrime K →+* V)
    (ho : ∀ x, algebraMap V K' (o x) = j x) {π : la.valuationSubringAtPrime K}
    (hπ : Irreducible π) (hoπ : Irreducible (o π)) : OverLa la V j 1 := by
  have hall := valV_ringHom_eq_valuation la j o ho hπ hoπ
  unfold OverLa vV vLa
  refine ⟨Nat.one_pos, fun a => ?_⟩
  rw [hall a, Nat.cast_one, _root_.one_mul]

theorem valV_eq_pow_of_overLa {j : K →+* K'} {e : ℕ} (ho : OverLa la V j e) (a : K) :
    valV V (j a) = la.valuation K a ^ e := by
  unfold OverLa vV vLa at ho
  obtain ⟨he, hlog⟩ := ho
  by_cases ha : a = 0
  · subst ha
    rw [map_zero, map_zero, map_zero, zero_pow he.ne']
  have h1 : valV V (j a) ≠ 0 := (Valuation.ne_zero_iff _).2 ((map_ne_zero j).2 ha)
  have h2 : la.valuation K a ^ e ≠ 0 := pow_ne_zero e ((Valuation.ne_zero_iff _).2 ha)
  have hk := hlog a
  rw [← WithZero.exp_log h1, ← WithZero.exp_log h2, WithZero.log_pow, WithZero.exp_inj, nsmul_eq_mul]
  linarith

private theorem valuation_lt_one_of_mem_maximalIdeal' (x : la.valuationSubringAtPrime K)
    (hx : x ∈ IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) : la.valuation K (x : K) < 1 :=
  lt_of_le_of_ne ((mem_atPrime_iff la (x : K)).1 x.2)
    (fun h => ((IsLocalRing.mem_maximalIdeal x).1 hx) ((isUnit_atPrime_iff la x).2 h))

theorem exists_localHom_of_overLa {j : K →+* K'} {e : ℕ} (ho : OverLa la V j e) :
    ∃ o : la.valuationSubringAtPrime K →+* V, (∀ x, algebraMap V K' (o x) = j x) ∧
      ∀ x ∈ IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K),
        o x ∈ IsLocalRing.maximalIdeal V := by
  have he : 0 < e := by
    have h' := ho
    unfold OverLa at h'
    exact h'.1
  have hint : ∀ x : la.valuationSubringAtPrime K, j x ∈ (algebraMap V K').range := fun x =>
    RingHom.mem_range.2 (exists_algebraMap_eq_of_valV_le_one (by
      rw [valV_eq_pow_of_overLa ho]
      exact pow_le_one₀ zero_le ((mem_atPrime_iff la (x : K)).1 x.2)))
  have finj : Function.Injective (algebraMap V K') := IsFractionRing.injective V K'
  let E := RingEquiv.ofBijective (algebraMap V K').rangeRestrict
    ⟨fun a b hab => finj (congrArg Subtype.val hab), (algebraMap V K').rangeRestrict_surjective⟩
  let r := (j.comp (la.valuationSubringAtPrime K).subtype).codRestrict _ hint
  have hE : ∀ x, algebraMap V K' (E.symm (r x)) = j x := fun x =>
    congrArg Subtype.val (E.apply_symm_apply (r x))
  refine ⟨E.symm.toRingHom.comp r, hE, fun x hx => ?_⟩
  rw [← valV_algebraMap_lt_one_iff (K' := K')]
  change valV V (algebraMap V K' (E.symm (r x))) < 1
  rw [hE, valV_eq_pow_of_overLa ho]
  exact pow_lt_one₀ zero_le (valuation_lt_one_of_mem_maximalIdeal' x hx) he.ne'

private theorem maximalIdeal_adicCompletion_eq_span' {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ϖ : A} (hϖ : Irreducible ϖ) :
    IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) = Ideal.span {algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) ϖ} := by
  rw [AdicCompletion.maximalIdeal_eq_map, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
    Ideal.map_span, Set.image_singleton]

private theorem adicCompletion_eq_unit_mul_pow {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ϖ : A} (hϖ : Irreducible ϖ)
    (x : AdicCompletion (IsLocalRing.maximalIdeal A) A) (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : (AdicCompletion (IsLocalRing.maximalIdeal A) A)ˣ), x = u * algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) ϖ ^ n := by
  have hpow : ∀ k, IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) ^ k =
      Ideal.span {algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) ϖ ^ k} := fun k => by
    rw [maximalIdeal_adicCompletion_eq_span' hϖ, Ideal.span_singleton_pow]
  have hex : ∃ N, x ∉ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) ^ N := by
    by_contra h
    push_neg at h
    apply hx
    refine IsHausdorff.haus (I := IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) inferInstance x fun n => ?_
    simpa [SModEq.zero] using h n
  classical
  have hN0 : Nat.find hex ≠ 0 := fun h0 => Nat.find_spec hex (by rw [h0, pow_zero]; rw [Ideal.one_eq_top]; trivial)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hxn : x ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) ^ n := by
    by_contra h
    exact Nat.find_min hex (by omega) h
  rw [hpow, Ideal.mem_span_singleton'] at hxn
  obtain ⟨y, hy⟩ := hxn
  have hyu : IsUnit y := by
    by_contra hyn
    have hym : y ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) := (IsLocalRing.mem_maximalIdeal y).2 hyn
    rw [maximalIdeal_adicCompletion_eq_span' hϖ, Ideal.mem_span_singleton'] at hym
    obtain ⟨z, hz⟩ := hym
    have hN := Nat.find_spec hex
    rw [hn, hpow, Ideal.mem_span_singleton'] at hN
    exact hN ⟨z, by rw [← hy, ← hz, pow_succ]; ring⟩
  exact ⟨n, hyu.unit, by rw [IsUnit.unit_spec, hy]⟩

private theorem algebraMap_adicCompletion_injective' {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    Function.Injective (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := fun _ _ h =>
  AdicCompletion.of_injective (IsLocalRing.maximalIdeal A) A h

private theorem isDomain_adicCompletion_of_dvr' {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hp : ∀ k, algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) ϖ ^ k ≠ 0 := fun k h => by
    rw [← map_pow] at h
    exact pow_ne_zero k hϖ.ne_zero (algebraMap_adicCompletion_injective' (by rw [h, map_zero]))
  have hnzd : NoZeroDivisors (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra hne
    push_neg at hne
    obtain ⟨n, u, rfl⟩ := adicCompletion_eq_unit_mul_pow hϖ a hne.1
    obtain ⟨m, v, rfl⟩ := adicCompletion_eq_unit_mul_pow hϖ b hne.2
    apply hp (n + m)
    have h2 : ((u * v : (AdicCompletion (IsLocalRing.maximalIdeal A) A)ˣ) : AdicCompletion (IsLocalRing.maximalIdeal A) A) * algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) ϖ ^ (n + m) = 0 := by
      rw [← hab, Units.val_mul, pow_add]
      ring
    exact (Units.mul_right_eq_zero (u * v)).1 h2
  exact NoZeroDivisors.to_isDomain _

private theorem irreducible_algebraMap_adicCompletion' {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)] {ϖ : A} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) ϖ) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
    (fun h => hϖ.ne_zero (algebraMap_adicCompletion_injective' (by rw [h, map_zero])))
    (maximalIdeal_adicCompletion_eq_span' hϖ)

private theorem isDVR_adicCompletion_of_isDomain {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)] :
    IsDiscreteValuationRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) ϖ, irreducible_algebraMap_adicCompletion' hϖ, fun {x} hx => ?_⟩
  obtain ⟨n, u, rfl⟩ := adicCompletion_eq_unit_mul_pow hϖ x hx
  exact ⟨n, u, mul_comm _ _⟩

end Place

theorem exists_initial_completion :
    ∀ (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)), ∃ (T₀ : CDVR) (io₀ : K →+* T₀.Fr), OverLa la T₀.V io₀ 1 ∧ T₀.FinRes ∧ ∀ (T : CDVR) (io : K →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∃ (g : T₀.V →+* T.V) (χ : T₀.Fr →+* T.Fr), IsLocalHom g ∧ χ.comp io₀ = io ∧ χ.comp (algebraMap T₀.V T₀.Fr) = (algebraMap T.V T.Fr).comp g ∧ ∀ ϖ : T₀.V, Irreducible ϖ → vV (K' := T.Fr) T.V (algebraMap T.V T.Fr (g ϖ)) = e := by
  intro K _ _ la
  have := la.isPrime
  have := la.isMaximal
  have hdvr : IsDiscreteValuationRing (la.valuationSubringAtPrime K) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) la.ne_bot _
  have hdom : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) := isDomain_adicCompletion_of_dvr'
  have hcdvr : IsDiscreteValuationRing (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) := isDVR_adicCompletion_of_isDomain
  have hch : CharZero (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) := by
    have : CharZero (la.valuationSubringAtPrime K) :=
      (RingHom.charZero_iff (ϕ := (la.valuationSubringAtPrime K).subtype) Subtype.val_injective).2 inferInstance
    exact (RingHom.charZero_iff (ϕ := algebraMap (la.valuationSubringAtPrime K) (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K))) algebraMap_adicCompletion_injective').1 inferInstance
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (la.valuationSubringAtPrime K)
  have hpπ := irreducible_algebraMap_adicCompletion' (A := la.valuationSubringAtPrime K) hπ
  have hinj : Function.Injective ((algebraMap (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)))).comp
      (algebraMap (la.valuationSubringAtPrime K) (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)))) :=
    (IsFractionRing.injective (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)))).comp algebraMap_adicCompletion_injective'
  obtain ⟨io₀, hio₀⟩ : ∃ f : K →+* FractionRing (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)), ∀ x : la.valuationSubringAtPrime K,
      f (algebraMap (la.valuationSubringAtPrime K) K x) = algebraMap (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) _ (algebraMap (la.valuationSubringAtPrime K) (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) x) :=
    ⟨IsFractionRing.lift hinj, fun x => IsFractionRing.lift_algebraMap hinj x⟩
  refine ⟨{ V := AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K) }, io₀, ?_, ?_, ?_⟩
  · exact overLa_one_of_irreducible io₀ (algebraMap (la.valuationSubringAtPrime K) (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K))) (fun x => (hio₀ x).symm) hπ hpπ
  · haveI : Finite (IsLocalRing.ResidueField (la.valuationSubringAtPrime K)) :=
      Finite.of_equiv _ (IsLocalization.AtPrime.equivQuotMaximalIdeal la.asIdeal (la.valuationSubringAtPrime K)).toEquiv
    exact Finite.of_surjective _ (AdicCompletion.residueField_map_bijective (la.valuationSubringAtPrime K)).2
  intro T io e hT
  obtain ⟨o, ho, hloc⟩ := exists_localHom_of_overLa hT
  have hk : (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)).map o ^ 1 ≤ IsLocalRing.maximalIdeal T.V := by
    rw [pow_one, Ideal.map_le_iff_le_comap]
    exact fun x hx => hloc x hx
  obtain ⟨g, hg, -⟩ := exists_extend_adicCompletion o (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K))
    (IsLocalRing.maximalIdeal T.V) hk
  have hoLoc : IsLocalHom o := ⟨fun a ha => by
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal _).1 (hloc a ((IsLocalRing.mem_maximalIdeal a).2 h)) ha⟩
  have hgLoc : IsLocalHom g := by
    have : IsLocalHom (g.comp (algebraMap (la.valuationSubringAtPrime K) (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)))) := by rw [hg]; exact hoLoc
    exact isLocalHom_of_extend_adicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)).fg_of_isNoetherianRing g
  have hgπ : g (algebraMap (la.valuationSubringAtPrime K) (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) π) = o π := by rw [← RingHom.comp_apply, hg]
  have hoπ : o π ≠ 0 := fun h0 => by
    have h1 := ho π
    rw [h0, map_zero] at h1
    exact hπ.ne_zero (Subtype.ext ((map_eq_zero io).1 h1.symm))
  have ginj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨n, u, rfl⟩ := adicCompletion_eq_unit_mul_pow hπ x hx0
    rw [map_mul, map_pow, hgπ] at hx
    exact pow_ne_zero n hoπ ((IsUnit.mul_right_eq_zero (u.isUnit.map g)).1 hx)
  have hginj : Function.Injective ((algebraMap T.V T.Fr).comp g) :=
    (IsFractionRing.injective T.V T.Fr).comp ginj
  obtain ⟨χ, hχ⟩ : ∃ χ : FractionRing (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) →+* T.Fr, ∀ y,
      χ (algebraMap (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) _ y) = algebraMap T.V T.Fr (g y) :=
    ⟨IsFractionRing.lift (A := AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) (K := FractionRing (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K))) hginj,
      fun y => IsFractionRing.lift_algebraMap (A := AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) (K := FractionRing (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K))) hginj y⟩
  refine ⟨g, χ, hgLoc, ?_, RingHom.ext hχ, ?_⟩
  · refine IsLocalization.ringHom_ext (nonZeroDivisors (la.valuationSubringAtPrime K)) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply]
    rw [hio₀, hχ, ← RingHom.comp_apply g, hg]
    exact ho x
  · intro ϖ hϖ
    obtain ⟨u, rfl⟩ := IsDiscreteValuationRing.associated_of_irreducible _ hpπ hϖ
    unfold vV
    rw [map_mul, map_mul, map_mul, hgπ, valV_algebraMap_of_isUnit ((u.isUnit).map g), _root_.mul_one,
      ho π, valV_eq_pow_of_overLa hT, valuation_of_irreducible la hπ, ← WithZero.exp_nsmul,
      WithZero.log_exp]
    simp

end GlobalTheory.PlaceCompletion
