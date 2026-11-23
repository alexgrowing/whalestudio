import Mathlib
import GroundTheory.GlobalFields.TateThesis.EulerFactorsFourierFinite
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace
import GroundTheory.GlobalFields.Artin.ConductorOneDim
import GroundTheory.AutomorphicForms.GL2.FiniteAdeleDecomp
import GroundTheory.LocalFields.LocalZeta

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory WithZero
  GroundTheory.LocalField IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar continuous_localChar)
open scoped NumberField.AdeleRing ENNReal NNReal

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

section Valuation

variable {v : HeightOneSpectrum (𝓞 K)}

theorem residueCard_adicCompletion : residueCard (v.adicCompletion K) = Ideal.absNorm v.asIdeal :=
  natCard_residueField_adicCompletion v

theorem valued_eq_exp_neg_ord {x : v.adicCompletion K} (hx : x ≠ 0) :
    Valued.v x = exp (-ord x) := by
  have h1 := norm_eq_absNorm_zpow_neg_ord v hx
  have h2 := normalizedAbv_eq_zpow v hx
  rw [normalizedAbv_apply] at h2
  have hN : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
    rw [← residueCard_adicCompletion]
    exact_mod_cast one_lt_residueCard (K := v.adicCompletion K)
  have h := zpow_right_injective₀ (a := (Ideal.absNorm v.asIdeal : ℝ)) (by linarith) hN.ne'
    (h2.symm.trans h1)
  rw [← exp_log ((Valued.v).ne_zero_iff.2 hx)]
  exact congrArg exp h

theorem mem_valBall_iff_valued {n : ℤ} {x : v.adicCompletion K} :
    x ∈ valBall (v.adicCompletion K) n ↔ Valued.v x ≤ exp (-n) := by
  by_cases hx : x = 0
  · subst hx
    simp only [map_zero, zero_le, iff_true]
    exact zero_mem _
  · rw [mem_valBall_iff_le_ord hx, valued_eq_exp_neg_ord hx, exp_le_exp]
    omega

theorem valued_eq_one_iff_ord {x : v.adicCompletion K} (hx : x ≠ 0) :
    Valued.v x = 1 ↔ ord x = 0 := by
  rw [valued_eq_exp_neg_ord hx, ← exp_zero, exp_inj]
  omega

end Valuation

section AddChar

variable (v : HeightOneSpectrum (𝓞 K))

theorem isTrivialOn_localAdelicChar_iff (n : ℤ) :
    IsTrivialOn (localAdelicChar K v) n ↔ -differentExp v ≤ n := by
  have hM : ∀ a ∈ v.adicCompletionIntegers K, ∀ x ∈ valBall (v.adicCompletion K) n,
      a * x ∈ valBall (v.adicCompletion K) n := by
    intro a ha x hx
    rw [mem_valBall_iff_valued] at hx ⊢
    rw [map_mul]
    calc Valued.v a * Valued.v x ≤ 1 * Valued.v x := by
          gcongr
          exact (mem_adicCompletionIntegers _ _ _).1 ha
      _ = Valued.v x := one_mul _
      _ ≤ exp (-n) := hx
  change (∀ x ∈ valBall (v.adicCompletion K) n, localAdelicChar K v x = 1) ↔ _
  rw [forall_localAdelicChar_eq_one_iff_le v _ hM]
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hx : ((unifUnit (v.adicCompletion K) ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈
        valBall (v.adicCompletion K) n := by
      rw [mem_valBall_iff_le_ord (Units.ne_zero _), ord_unifUnit_zpow]
    have h2 := (mem_localInvDifferent_iff_valued v _).1 (h hx)
    rw [valued_eq_exp_neg_ord (Units.ne_zero _), ord_unifUnit_zpow, exp_le_exp] at h2
    change -n ≤ differentExp v at h2
    omega
  · intro h x hx
    rw [mem_localInvDifferent_iff_valued]
    exact ((mem_valBall_iff_valued).1 hx).trans (exp_le_exp.2 (by change -n ≤ differentExp v; omega))

theorem localAdelicChar_ne_one : localAdelicChar K v ≠ 1 := by
  intro h
  have h1 : IsTrivialOn (localAdelicChar K v) (-differentExp v - 1) := fun x _ ↦ by
    rw [h]
    rfl
  have := (isTrivialOn_localAdelicChar_iff v _).1 h1
  omega

theorem addCharConductor_localAdelicChar :
    addCharConductor (localAdelicChar K v) = -differentExp v := by
  have hc := continuous_localAdelicChar v
  have hne := localAdelicChar_ne_one v
  apply le_antisymm
  · exact (isTrivialOn_iff hc hne _).1 ((isTrivialOn_localAdelicChar_iff v _).2 le_rfl)
  · exact (isTrivialOn_localAdelicChar_iff v _).1 (isTrivialOn_addCharConductor hc hne)

end AddChar

namespace HeckeCharacter

variable (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K))

theorem ker_localChar :
    (localChar χ v).ker = (χ.localComponent v : (v.adicCompletion K)ˣ →* Circle).ker := by
  ext a
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Units.val_eq_one, coe_localChar]
  exact Circle.coe_eq_one

theorem unitFiltrationUnits_le_ker_localChar_iff (n : ℕ) :
    unitFiltrationUnits (v.adicCompletion K) n ≤ (localChar χ v).ker ↔
      multiplicity v.asIdeal χ.conductor ≤ n := by
  have hloc : ((χ.toIdele.comp ofFinite).comp (finiteUnitsSingle v)) =
      (χ.localComponent v : (v.adicCompletion K)ˣ →* Circle) := by
    ext a
    simp only [MonoidHom.comp_apply, ofFinite_finiteUnitsSingle]
    rfl
  have hcont : Continuous ((χ.toIdele.comp ofFinite).comp (finiteUnitsSingle v)) :=
    (χ.continuous_toIdele.comp continuous_ofFinite).comp (continuous_finiteUnitsSingle v)
  rw [unitFiltrationUnits_eq_unitsLevel, ker_localChar, ← hloc,
    unitsLevel_le_ker_iff v Circle.noSmallSubgroups _ hcont]
  change conductorExponentAt (χ.toIdele.comp ofFinite) v ≤ n ↔ _
  rw [← χ.multiplicity_conductor]

theorem quasiCharConductor_localChar :
    quasiCharConductor (localChar χ v) = multiplicity v.asIdeal χ.conductor := by
  apply le_antisymm
  · exact Nat.sInf_le ((χ.unitFiltrationUnits_le_ker_localChar_iff v _).2 le_rfl)
  · exact (χ.unitFiltrationUnits_le_ker_localChar_iff v _).1
      (unitFiltrationUnits_quasiCharConductor_le_ker (continuous_localChar χ v))

theorem isUnramifiedChar_localChar_iff :
    IsUnramifiedChar (localChar χ v) ↔ ¬ v.asIdeal ∣ χ.conductor := by
  rw [IsUnramifiedChar, χ.unitFiltrationUnits_le_ker_localChar_iff v 0, Nat.le_zero,
    multiplicity_eq_zero]

theorem isLocallyConstant_finiteTest : IsLocallyConstant (χ.finiteTest v) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x₀ ↦ ?_
  set m : ℤ := (multiplicity v.asIdeal χ.conductor : ℤ)
  have hW : {x : v.adicCompletion K | x - x₀ ∈ valBall (v.adicCompletion K) m} ∈ nhds x₀ :=
    ((isOpen_valBall m).preimage (continuous_id.sub continuous_const)).mem_nhds
      (show x₀ - x₀ ∈ valBall (v.adicCompletion K) m by rw [sub_self]; exact zero_mem _)
  filter_upwards [hW] with x hx
  have := χ.finiteTest_add x₀ (h := x - x₀) ((mem_valBall_iff_valued).1 hx)
  rwa [add_sub_cancel] at this

theorem continuous_finiteTest : Continuous (χ.finiteTest v) :=
  (χ.isLocallyConstant_finiteTest v).continuous

theorem hasCompactSupport_finiteTest_mul (g : v.adicCompletion K → ℂ) :
    HasCompactSupport fun y ↦ χ.finiteTest v y * g y := by
  refine HasCompactSupport.intro (isCompact_adicCompletionIntegers v) fun y hy ↦ ?_
  rw [SetLike.mem_coe, mem_adicCompletionIntegers, not_le] at hy
  rw [χ.finiteTest_eq_zero hy, zero_mul]

theorem integrable_finiteTest_mul_localAdelicChar (b : v.adicCompletion K) :
    Integrable (fun y ↦ χ.finiteTest v y * (localAdelicChar K v (b * y) : ℂ))
      (haarIntegers (v.adicCompletion K)) :=
  ((χ.continuous_finiteTest v).mul (continuous_subtype_val.comp
    ((continuous_localAdelicChar v).comp (continuous_const_mul b)))).integrable_of_hasCompactSupport
    (χ.hasCompactSupport_finiteTest_mul v _)

theorem localEpsilon_half_of_not_dvd (hv : ¬ v.asIdeal ∣ χ.conductor) (a : (v.adicCompletion K)ˣ)
    (ha : ord (a : v.adicCompletion K) = differentExp v) :
    localEpsilon (localChar χ v) (localAdelicChar K v) (1 / 2) = (χ.localComponent v a : ℂ) := by
  have hu := (χ.isUnramifiedChar_localChar_iff v).2 hv
  rw [localEpsilon_of_isUnramified hu, addCharConductor_localAdelicChar, sub_self, mul_zero,
    Complex.cpow_zero, mul_one, ← coe_localChar, quasiChar_apply_of_isUnramified hu a, ha, neg_neg,
    Units.val_zpow_eq_zpow_val]

theorem localEpsilon_half_of_dvd (hv : v.asIdeal ∣ χ.conductor) (a : (v.adicCompletion K)ˣ)
    (ha : ord (a : v.adicCompletion K) = χ.condExp v + differentExp v) :
    localEpsilon (localChar χ v) (localAdelicChar K v) (1 / 2) =
      (Real.sqrt ((Ideal.absNorm v.asIdeal ^ multiplicity v.asIdeal χ.conductor : ℕ) : ℝ) : ℂ) *
        (χ.localComponent v a : ℂ) *
        ∫ y, χ.finiteTest v y * (localAdelicChar K v ((a : v.adicCompletion K)⁻¹ * y) : ℂ)
          ∂haarIntegers (v.adicCompletion K) := by
  have hr : ¬ IsUnramifiedChar (localChar χ v) := fun h ↦ ((χ.isUnramifiedChar_localChar_iff v).1 h) hv
  have hn := addCharConductor_localAdelicChar v
  have hc := χ.quasiCharConductor_localChar v
  have hf : χ.condExp v = (multiplicity v.asIdeal χ.conductor : ℤ) := χ.condExp_eq v
  set m := multiplicity v.asIdeal χ.conductor with hm
  set d := differentExp v with hd
  have ha0 : (a : v.adicCompletion K) ≠ 0 := a.ne_zero
  have hai : (a : v.adicCompletion K)⁻¹ ≠ 0 := inv_ne_zero ha0
  rw [localEpsilon_of_not_isUnramified hr, hn, hc]
  set A : Set (v.adicCompletion K) :=
    (valBall (v.adicCompletion K) (-d - (m : ℤ)) : Set (v.adicCompletion K)) \
      valBall (v.adicCompletion K) (-d - (m : ℤ) + 1) with hAdef
  have hA : MeasurableSet A := (measurableSet_valBall _).diff (measurableSet_valBall _)
  set F : v.adicCompletion K → ℂ := fun x ↦ quasiCharExt (localChar χ v)⁻¹ x *
    ((modulus x : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * (localAdelicChar K v x : ℂ) with hFdef
  set M : ℝ := (modulus ((a : v.adicCompletion K)⁻¹) : ℝ) with hMdef
  have hM0 : 0 < M := NNReal.coe_pos.2 (modulus_pos hai)
  rw [← integral_indicator hA]
  unfold LocalField.selfDualMeasure
  rw [hn, integral_smul_nnreal_measure]

  have hsub : ∫ x, A.indicator F x ∂haarIntegers (v.adicCompletion K) =
      M • ∫ y, A.indicator F ((a : v.adicCompletion K)⁻¹ * y) ∂haarIntegers (v.adicCompletion K) := by
    rw [integral_comp_mul_left (haarIntegers (v.adicCompletion K)) hai, smul_smul,
      mul_inv_cancel₀ hM0.ne', one_smul]

  have hpt : ∀ y, A.indicator F ((a : v.adicCompletion K)⁻¹ * y) =
      (χ.localComponent v a : ℂ) * ((M : ℂ) ^ (-(1 / 2 : ℂ))) *
        (χ.finiteTest v y * (localAdelicChar K v ((a : v.adicCompletion K)⁻¹ * y) : ℂ)) := by
    intro y
    by_cases hy : Valued.v y = 1
    · have hy0 : y ≠ 0 := fun h ↦ by simp [h] at hy
      set u : (v.adicCompletion K)ˣ := Units.mk0 y hy0
      have hu : ((a⁻¹ * u : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
          (a : v.adicCompletion K)⁻¹ * y := by
        simp [u]
      have hyo : ord y = 0 := (valued_eq_one_iff_ord hy0).1 hy
      have hmem : (a : v.adicCompletion K)⁻¹ * y ∈ A := by
        rw [hAdef, mem_shellSet_iff (mul_ne_zero hai hy0), ord_mul hai hy0, ord_inv ha0, hyo, ha, hf]
        ring
      rw [Set.indicator_of_mem hmem, hFdef]
      simp only
      rw [← hu, quasiCharExt_units, MonoidHom.inv_apply, map_mul, map_inv, Units.val_inv_eq_inv_val,
        Units.val_mul, Units.val_inv_eq_inv_val, coe_localChar, coe_localChar, hu, modulus_mul,
        modulus_of_ne_zero hy0, hyo, neg_zero, zpow_zero, mul_one]
      have hft : χ.finiteTest v y = ((χ.localComponent v u : ℂ))⁻¹ := χ.finiteTest_of_dvd hv u hy
      rw [← hMdef, hft]
      simp only [mul_inv, inv_inv]
      ring
    · have hnot : (a : v.adicCompletion K)⁻¹ * y ∉ A := by
        by_cases hy0 : y = 0
        · rw [hy0, mul_zero]
          exact zero_notMem_shellSet _
        · rw [hAdef, mem_shellSet_iff (mul_ne_zero hai hy0), ord_mul hai hy0, ord_inv ha0, ha, hf]
          intro h
          exact hy ((valued_eq_one_iff_ord hy0).2 (by linarith))
      rw [Set.indicator_of_notMem hnot, χ.finiteTest_eq_zero_of_dvd hv hy, zero_mul, mul_zero]
  rw [hsub, integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]

  have hq : (residueCard (v.adicCompletion K) : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by
    rw [residueCard_adicCompletion]
  have hN : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    rw [← hq]
    exact_mod_cast (zero_lt_one.trans (one_lt_residueCard (K := v.adicCompletion K)))
  have hMe : M = (Ideal.absNorm v.asIdeal : ℝ) ^ ((m : ℝ) + d) := by
    rw [hMdef, modulus_of_ne_zero hai, NNReal.coe_zpow, NNReal.coe_natCast, hq, ord_inv ha0, neg_neg,
      ha, hf, ← Real.rpow_intCast]
    push_cast
    ring_nf
  have hkey : (((residueCard (v.adicCompletion K) : ℝ≥0) ^ (((-d : ℤ) : ℝ) / 2) : ℝ≥0) : ℝ) * M *
      M ^ (-(1 / 2 : ℝ)) = Real.sqrt ((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℝ) := by
    rw [NNReal.coe_rpow, NNReal.coe_natCast, hq, hMe, ← Real.rpow_mul hN.le, Real.sqrt_eq_rpow,
      Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_add hN,
      ← Real.rpow_add hN]
    congr 1
    push_cast
    ring
  have hMc : (M : ℂ) ^ (-(1 / 2 : ℂ)) = ((M ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hM0.le]
    push_cast
    ring_nf
  rw [hMc, NNReal.smul_def, Complex.real_smul, Complex.real_smul, ← hkey]
  push_cast
  ring

end HeckeCharacter

end

end GroundTheory.Global
