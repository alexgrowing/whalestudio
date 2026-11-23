import Mathlib
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import GroundTheory.GlobalFields.TateThesis.HeckeTheoremFE
import GroundTheory.GlobalFields.TateThesis.FiniteAdeleScaling
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory WithZero
  GroundTheory.LocalField IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar adeleAtS awayIntegral mem_awayIntegral
  integral_finiteAdele_local_awayIntegral haarS partAt awayPart partAt_mul_awayPart
  toIdele_ofFinite_partAt finiteComponent_awayPart)
open scoped NumberField.AdeleRing ENNReal NNReal

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem sqrt_natCast_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    Real.sqrt ((∏ i ∈ s, f i : ℕ) : ℝ) = ∏ i ∈ s, Real.sqrt (f i : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul,
      Real.sqrt_mul (Nat.cast_nonneg _), ih]

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

theorem mem_units_of_isIntegralUnitAt {b : (FiniteAdeleRing (𝓞 K) K)ˣ} {v : HeightOneSpectrum (𝓞 K)}
    (h : IsIntegralUnitAt b v) :
    finiteComponent v b ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  rw [Submonoid.mem_units_iff]
  refine ⟨?_, ?_⟩
  · rw [coe_finiteComponent]
    exact h.1
  · rw [← map_inv, coe_finiteComponent]
    exact h.2

theorem finite_mulSupport_localComponent (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (Function.mulSupport fun v ↦ (χ.localComponent v (finiteComponent v b) : ℂ)).Finite := by
  refine ((finite_setOf_not_isIntegralUnitAt b).union χ.finite_setOf_dvd_conductor).subset
    fun v hv ↦ ?_
  by_contra h
  rw [Set.mem_union, not_or] at h
  have h1 : IsIntegralUnitAt b v := not_not.1 h.1
  have h2 : ¬ v.asIdeal ∣ χ.conductor := h.2
  apply hv
  change (χ.localComponent v (finiteComponent v b) : ℂ) = 1
  rw [χ.localComponent_eq_one_of_not_dvd h2 (mem_units_of_isIntegralUnitAt h1), Circle.coe_one]

theorem toIdele_ofFinite_eq_finprod (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (χ.toIdele (ofFinite b) : ℂ) = ∏ᶠ v, (χ.localComponent v (finiteComponent v b) : ℂ) := by
  classical
  set T : Finset (HeightOneSpectrum (𝓞 K)) :=
    ((finite_setOf_not_isIntegralUnitAt b).union χ.finite_setOf_dvd_conductor).toFinset with hTdef
  have hT : ∀ w ∉ T, IsIntegralUnitAt b w ∧ ¬ w.asIdeal ∣ χ.conductor := by
    intro w hw
    rw [hTdef, Set.Finite.mem_toFinset, Set.mem_union, not_or] at hw
    exact ⟨not_not.1 hw.1, hw.2⟩
  have haway : χ.toIdele (ofFinite (awayPart T b)) = 1 := by
    have hmem : awayPart T b ∈ idealLevel χ.conductor := by
      rw [idealLevel, mem_finiteLevel]
      intro w
      rw [finiteComponent_awayPart]
      split_ifs with hw
      · exact one_mem _
      · obtain ⟨h1, h2⟩ := hT w hw
        rw [multiplicity_eq_zero.2 h2, unitsLevel_zero]
        exact mem_units_of_isIntegralUnitAt h1
    exact χ.map_idealLevel_conductor_le_ker (Subgroup.mem_map_of_mem ofFinite hmem)
  conv_lhs => rw [← partAt_mul_awayPart T b]
  rw [map_mul, map_mul, haway, mul_one, toIdele_ofFinite_partAt]
  symm
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ ?_
  by_contra hvT
  apply hv
  obtain ⟨h1, h2⟩ := hT v hvT
  change (χ.localComponent v (finiteComponent v b) : ℂ) = 1
  rw [χ.localComponent_eq_one_of_not_dvd h2 (mem_units_of_isIntegralUnitAt h1), Circle.coe_one]

theorem conductor_eq_prod :
    χ.conductor = ∏ v ∈ χ.conductorPrimes, v.asIdeal ^ multiplicity v.asIdeal χ.conductor := by
  conv_lhs => rw [conductor, IdeleGroup.conductor]
  rw [finprod_congr fun v ↦ by rw [← χ.multiplicity_conductor v]]
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ ?_
  by_contra hvS
  apply hv
  change v.asIdeal ^ multiplicity v.asIdeal χ.conductor = 1
  rw [multiplicity_eq_zero.2 fun h ↦ hvS (χ.mem_conductorPrimes.2 h), pow_zero]

theorem absNorm_conductor :
    Ideal.absNorm χ.conductor =
      ∏ v ∈ χ.conductorPrimes, Ideal.absNorm v.asIdeal ^ multiplicity v.asIdeal χ.conductor := by
  conv_lhs => rw [χ.conductor_eq_prod]
  rw [map_prod]
  exact Finset.prod_congr rfl fun v _ ↦ map_pow _ _ _

variable {χ}

theorem valued_inv_of_toFractionalIdeal_eq {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) =
      exp (χ.condExp v + differentExp v) := by
  have h1 := χ.valued_of_toFractionalIdeal_eq hδ v
  have h2 := congrArg Valued.v (units_mul_inv_apply δ v)
  rw [map_mul, map_one, h1] at h2
  calc Valued.v (((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v)
      = exp (χ.condExp v + differentExp v) *
          (exp (-(χ.condExp v + differentExp v)) *
            Valued.v (((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v)) := by
        rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
    _ = exp (χ.condExp v + differentExp v) := by rw [h2, mul_one]

theorem inv_apply_eq {δ : (FiniteAdeleRing (𝓞 K) K)ˣ} (v : HeightOneSpectrum (𝓞 K)) :
    ((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v =
      ((finiteComponent v δ : (v.adicCompletion K)ˣ) : v.adicCompletion K)⁻¹ := by
  rw [coe_finiteComponent]
  exact (eq_inv_of_mul_eq_one_right (units_mul_inv_apply δ v))

variable (χ)

theorem finiteTestFun_mul_finiteAdelicChar_eq {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    (x : FiniteAdeleRing (𝓞 K) K) :
    χ.finiteTestFun x *
        (finiteAdelicChar K (x * ((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K)) : ℂ) =
      (∏ v : χ.conductorPrimes, χ.finiteTest v.1 (x v.1) *
          (localAdelicChar K v.1
            (((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v.1 * x v.1) : ℂ)) *
        (awayIntegral χ.conductorPrimes : Set (FiniteAdeleRing (𝓞 K) K)).indicator 1 x := by
  classical
  set S := χ.conductorPrimes with hSdef
  set e : FiniteAdeleRing (𝓞 K) K := ((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K)
    with hedef
  by_cases hx : x ∈ awayIntegral S
  · rw [Set.indicator_of_mem (SetLike.mem_coe.2 hx), Pi.one_apply, mul_one]
    have hxv : ∀ w ∉ S, Valued.v (x w) ≤ 1 := fun w hw ↦
      (mem_adicCompletionIntegers _ _ _).1 (mem_awayIntegral.1 hx w hw)
    have hf : χ.finiteTestFun x = ∏ v : S, χ.finiteTest v.1 (x v.1) := by
      rw [finiteTestFun, Finset.prod_coe_sort S (fun v : HeightOneSpectrum (𝓞 K) ↦ χ.finiteTest v (x v))]
      refine finprod_eq_prod_of_mulSupport_subset _ fun w hw ↦ ?_
      by_contra hwS
      exact hw (χ.finiteTest_eq_one (fun h ↦ hwS (χ.mem_conductorPrimes.2 h)) (hxv w hwS))
    set a : (v : S) → v.1.adicCompletion K := fun v ↦ (x * e) v.1 with hadef
    have hr : x * e - GroundTheory.Automorphic.GodementSection.adeleSingleS S a ∈ finiteInvDifferent K := by
      intro w
      change (x * e) w - GroundTheory.Automorphic.GodementSection.adeleSingleS S a w ∈ localInvDifferent w
      by_cases hw : w ∈ S
      · rw [GroundTheory.Automorphic.GodementSection.adeleSingleS_apply_of_mem S a ⟨w, hw⟩, sub_self]
        exact zero_mem _
      · rw [GroundTheory.Automorphic.GodementSection.adeleSingleS_apply_of_notMem S a hw, sub_zero,
          mem_localInvDifferent_iff_valued]
        change Valued.v (x w * e w) ≤ exp (differentExp w)
        rw [map_mul, hedef, valued_inv_of_toFractionalIdeal_eq hδ w,
          χ.condExp_eq_zero fun h ↦ hw (χ.mem_conductorPrimes.2 h), zero_add]
        calc Valued.v (x w) * exp (differentExp w) ≤ 1 * exp (differentExp w) := by
              gcongr
              exact hxv w hw
          _ = exp (differentExp w) := one_mul _
    have hψc : finiteAdelicChar K (x * e) = ∏ v : S, localAdelicChar K v.1 (e v.1 * x v.1) := by
      have hsplit : x * e = GroundTheory.Automorphic.GodementSection.adeleSingleS S a +
          (x * e - GroundTheory.Automorphic.GodementSection.adeleSingleS S a) := by abel
      rw [hsplit, AddChar.map_add_eq_mul, finiteAdelicChar_eq_one_of_mem hr, mul_one]
      change finiteAdelicChar K (∑ v : S, finiteAdeleSingleAdd v.1 (a v)) = _
      rw [addChar_map_finsetSum]
      refine Finset.prod_congr rfl fun v _ ↦ ?_
      rw [finiteAdelicChar_finiteAdeleSingleAdd]
      change localAdelicChar K v.1 (x v.1 * e v.1) = _
      rw [mul_comm]
    have hψ : (finiteAdelicChar K (x * e) : ℂ) =
        ∏ v : S, (localAdelicChar K v.1 (e v.1 * x v.1) : ℂ) := by
      rw [hψc]
      exact map_prod Circle.coeHom _ _
    rw [hf, hψ, ← Finset.prod_mul_distrib]
  · rw [Set.indicator_of_notMem (fun h ↦ hx (SetLike.mem_coe.1 h)), mul_zero]
    obtain ⟨w, hw, hxw⟩ : ∃ w ∉ S, x w ∉ w.adicCompletionIntegers K := by
      by_contra h
      push Not at h
      exact hx (mem_awayIntegral.2 h)
    rw [mem_adicCompletionIntegers, not_le] at hxw
    rw [χ.finiteTestFun_eq_zero hxw, zero_mul]

theorem finiteFourier_finiteTestFun_inv_eq {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit) :
    finiteFourier K χ.finiteTestFun ((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) =
      (((NNReal.sqrt ‖discr K‖₊)⁻¹ : ℝ≥0) : ℂ) *
        ∏ v : χ.conductorPrimes, ∫ y, χ.finiteTest v.1 y *
          (localAdelicChar K v.1
            (((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v.1 * y) : ℂ)
          ∂haarIntegers (v.1.adicCompletion K) := by
  set S := χ.conductorPrimes
  set e : FiniteAdeleRing (𝓞 K) K := ((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K)
  set g : (v : S) → v.1.adicCompletion K → ℂ := fun v y ↦
    χ.finiteTest v.1 y * (localAdelicChar K v.1 (e v.1 * y) : ℂ)
  have hF : Integrable (fun a : (v : S) → v.1.adicCompletion K ↦ ∏ v : S, g v (a v)) (haarS S) :=
    Integrable.fintype_prod_dep fun v ↦ χ.integrable_finiteTest_mul_localAdelicChar v.1 (e v.1)
  obtain ⟨-, h⟩ := integral_finiteAdele_local_awayIntegral hF
  have hpt : ∀ x : FiniteAdeleRing (𝓞 K) K, χ.finiteTestFun x * (finiteAdelicChar K (x * e) : ℂ) =
      (∏ v : S, g v (x v.1)) * (awayIntegral S : Set (FiniteAdeleRing (𝓞 K) K)).indicator 1 x :=
    fun x ↦ χ.finiteTestFun_mul_finiteAdelicChar_eq hδ x
  rw [finiteFourier, integral_congr_ae (Filter.Eventually.of_forall hpt),
    ← integral_fintype_prod_eq_prod]
  exact h

theorem ord_finiteComponent_of_toFractionalIdeal_eq {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    (v : HeightOneSpectrum (𝓞 K)) :
    ord ((finiteComponent v δ : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      χ.condExp v + differentExp v := by
  have h1 := χ.valued_of_toFractionalIdeal_eq hδ v
  rw [← coe_finiteComponent, valued_eq_exp_neg_ord (Units.ne_zero _), exp_inj] at h1
  omega

open Classical in

theorem localEpsilon_half_eq {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    (v : HeightOneSpectrum (𝓞 K)) :
    localEpsilon (localChar χ v) (localAdelicChar K v) (1 / 2) =
      (χ.localComponent v (finiteComponent v δ) : ℂ) *
        (if v ∈ χ.conductorPrimes then
          (Real.sqrt ((Ideal.absNorm v.asIdeal ^ multiplicity v.asIdeal χ.conductor : ℕ) : ℝ) : ℂ) *
            ∫ y, χ.finiteTest v y *
              (localAdelicChar K v (((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v * y) : ℂ)
              ∂haarIntegers (v.adicCompletion K)
        else 1) := by
  split_ifs with hv
  · rw [χ.localEpsilon_half_of_dvd v (χ.mem_conductorPrimes.1 hv) _
      (χ.ord_finiteComponent_of_toFractionalIdeal_eq hδ v), inv_apply_eq]
    ring
  · have hv' : ¬ v.asIdeal ∣ χ.conductor := fun h ↦ hv (χ.mem_conductorPrimes.2 h)
    rw [χ.localEpsilon_half_of_not_dvd v hv' _
      (by rw [χ.ord_finiteComponent_of_toFractionalIdeal_eq hδ v, χ.condExp_eq_zero hv', zero_add]),
      mul_one]

open Classical in

theorem finiteFourier_mul_eq_finprod_localEpsilon {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit) :
    finiteFourier K χ.finiteTestFun ((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) *
        (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ (1 / 2 : ℂ) =
      ∏ᶠ v, localEpsilon (localChar χ v) (localAdelicChar K v) (1 / 2) := by
  set S := χ.conductorPrimes with hSdef
  set I : HeightOneSpectrum (𝓞 K) → ℂ := fun v ↦ ∫ y, χ.finiteTest v y *
    (localAdelicChar K v (((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v * y) : ℂ)
    ∂haarIntegers (v.adicCompletion K) with hIdef
  set s : HeightOneSpectrum (𝓞 K) → ℂ := fun v ↦
    (Real.sqrt ((Ideal.absNorm v.asIdeal ^ multiplicity v.asIdeal χ.conductor : ℕ) : ℝ) : ℂ) with hsdef
  set c : HeightOneSpectrum (𝓞 K) → ℂ := fun v ↦ if v ∈ S then s v * I v else 1 with hcdef
  have hc : (Function.mulSupport c).Finite := S.finite_toSet.subset fun v hv ↦ by
    by_contra h
    exact hv (if_neg h)
  have hcS : ∏ᶠ v, c v = ∏ v ∈ S, s v * I v := by
    rw [finprod_eq_prod_of_mulSupport_subset c (s := S) fun v hv ↦ by
      by_contra h
      exact hv (if_neg h)]
    exact Finset.prod_congr rfl fun v hv ↦ if_pos hv
  rw [finprod_congr (χ.localEpsilon_half_eq hδ),
    finprod_mul_distrib (χ.finite_mulSupport_localComponent δ) hc, ← χ.toIdele_ofFinite_eq_finprod δ,
    hcS, χ.finiteFourier_finiteTestFun_inv_eq hδ]

  have hd0 : (0 : ℝ) ≤ |(discr K : ℝ)| := abs_nonneg _
  have hA0 : (0 : ℝ) ≤ χ.discrNormConductor := χ.discrNormConductor_pos.le
  have hA : (χ.discrNormConductor : ℂ) ^ (1 / 2 : ℂ) =
      (Real.sqrt |(discr K : ℝ)| : ℂ) * ∏ v ∈ S, s v := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hA0,
      ← Real.sqrt_eq_rpow, discrNormConductor, Real.sqrt_mul hd0, χ.absNorm_conductor,
      sqrt_natCast_prod, Complex.ofReal_mul, Complex.ofReal_prod]
  have hdisc : (((NNReal.sqrt ‖discr K‖₊)⁻¹ : ℝ≥0) : ℂ) * (Real.sqrt |(discr K : ℝ)| : ℂ) = 1 := by
    have hne : Real.sqrt |(discr K : ℝ)| ≠ 0 := by
      rw [Ne, Real.sqrt_eq_zero hd0, abs_eq_zero]
      exact_mod_cast discr_ne_zero K
    have h1 : (((NNReal.sqrt ‖discr K‖₊)⁻¹ : ℝ≥0) : ℝ) = (Real.sqrt |(discr K : ℝ)|)⁻¹ := by
      rw [NNReal.coe_inv, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
    rw [show (((NNReal.sqrt ‖discr K‖₊)⁻¹ : ℝ≥0) : ℂ) = ((((NNReal.sqrt ‖discr K‖₊)⁻¹ : ℝ≥0) : ℝ) : ℂ)
      from rfl, h1, Complex.ofReal_inv, inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 hne)]
  rw [hA, Finset.prod_mul_distrib, Finset.prod_coe_sort S I]
  linear_combination ((χ.toIdele (ofFinite δ) : ℂ) * (∏ v ∈ S, s v) * ∏ v ∈ S, I v) * hdisc

end HeckeCharacter

end

end GroundTheory.Global
