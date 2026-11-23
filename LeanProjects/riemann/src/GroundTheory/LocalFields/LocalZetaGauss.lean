import Mathlib
import GroundTheory.LocalFields.LocalZetaEpsilon

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Quotient

variable (K) in

abbrev unitsModFiltration (c : ℕ) : Type _ :=
  unitFiltrationUnits K 0 ⧸ (unitFiltrationUnits K c).subgroupOf (unitFiltrationUnits K 0)

instance finite_unitsModFiltration (c : ℕ) : Finite (unitsModFiltration K c) := by
  have : CompactSpace (unitFiltrationUnits K 0) :=
    isCompact_iff_compactSpace.mp isCompact_unitFiltrationUnits_zero
  refine Subgroup.quotient_finite_of_isOpen _ ?_
  rw [Subgroup.coe_subgroupOf]
  exact (isOpen_unitFiltrationUnits c).preimage continuous_subtype_val

noncomputable instance fintype_unitsModFiltration (c : ℕ) : Fintype (unitsModFiltration K c) :=
  Fintype.ofFinite _

def unitsModRep {c : ℕ} (t : unitsModFiltration K c) : Kˣ :=
  ((Quotient.out t : unitFiltrationUnits K 0) : Kˣ)

theorem unitsModRep_mem {c : ℕ} (t : unitsModFiltration K c) :
    unitsModRep t ∈ unitFiltrationUnits K 0 :=
  (Quotient.out t).2

def unitsModCoset {c : ℕ} (t : unitsModFiltration K c) : Set Kˣ :=
  (fun x => (unitsModRep t)⁻¹ * x) ⁻¹' (unitFiltrationUnits K c : Set Kˣ)

theorem mem_unitsModCoset {c : ℕ} {t : unitsModFiltration K c} {x : Kˣ} :
    x ∈ unitsModCoset t ↔ (unitsModRep t)⁻¹ * x ∈ unitFiltrationUnits K c := Iff.rfl

theorem mem_unitsModCoset_mk {c : ℕ} {x : Kˣ} (hx : x ∈ unitFiltrationUnits K 0) :
    x ∈ unitsModCoset (QuotientGroup.mk ⟨x, hx⟩ : unitsModFiltration K c) := by
  have h := QuotientGroup.out_eq' (QuotientGroup.mk ⟨x, hx⟩ : unitsModFiltration K c)
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  simpa [mem_unitsModCoset, unitsModRep] using h

theorem unitsModCoset_subset {c : ℕ} (t : unitsModFiltration K c) :
    unitsModCoset t ⊆ (unitFiltrationUnits K 0 : Set Kˣ) := by
  intro x hx
  have h := mul_mem (unitsModRep_mem t)
    (unitFiltrationUnits_antitone (Nat.zero_le c) (mem_unitsModCoset.mp hx))
  rwa [mul_inv_cancel_left] at h

theorem eq_of_mem_unitsModCoset {c : ℕ} {t t' : unitsModFiltration K c} {x : Kˣ}
    (h : x ∈ unitsModCoset t) (h' : x ∈ unitsModCoset t') : t = t' := by
  rw [← QuotientGroup.out_eq' t, ← QuotientGroup.out_eq' t', QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  have := mul_mem (mem_unitsModCoset.mp h) (inv_mem (mem_unitsModCoset.mp h'))
  simp only [mul_inv_rev, inv_inv] at this
  simpa [unitsModRep, mul_assoc] using this

end Quotient

variable [MeasurableSpace K] [BorelSpace K]

section Integral

theorem measurableSet_unitsModCoset {c : ℕ} (t : unitsModFiltration K c) :
    MeasurableSet (unitsModCoset t) :=
  (isOpen_unitFiltrationUnits c).measurableSet.preimage (measurable_const_mul _)

theorem multHaar_unitsModCoset {c : ℕ} (t : unitsModFiltration K c) :
    multHaar K (unitsModCoset t) = multHaar K (unitFiltrationUnits K c) :=
  measure_preimage_mul _ _ _

theorem multHaar_unitFiltrationUnits_lt_top (c : ℕ) :
    multHaar K (unitFiltrationUnits K c) < ∞ := by
  refine (measure_mono (unitFiltrationUnits_antitone (Nat.zero_le c))).trans_lt ?_
  rw [multHaar_unitFiltrationUnits_zero]
  exact ENNReal.one_lt_top

theorem setIntegral_units_eq_sum {c : ℕ} (G : Kˣ → ℂ)
    (hG : ∀ x ∈ unitFiltrationUnits K 0, ∀ w ∈ unitFiltrationUnits K c, G (x * w) = G x) :
    ∫ u in (unitFiltrationUnits K 0 : Set Kˣ), G u ∂multHaar K =
      ((multHaar K (unitFiltrationUnits K c)).toReal : ℂ) *
        ∑ t : unitsModFiltration K c, G (unitsModRep t) := by
  classical
  have hcover : (unitFiltrationUnits K 0 : Set Kˣ).indicator G =
      fun u => ∑ t : unitsModFiltration K c, (unitsModCoset t).indicator
        (fun _ => G (unitsModRep t)) u := by
    funext u
    by_cases hu : u ∈ (unitFiltrationUnits K 0 : Set Kˣ)
    · set t0 : unitsModFiltration K c := QuotientGroup.mk ⟨u, hu⟩
      have hu0 : u ∈ unitsModCoset t0 := mem_unitsModCoset_mk hu
      rw [Set.indicator_of_mem hu, Finset.sum_eq_single t0, Set.indicator_of_mem hu0]
      · have := hG _ (unitsModRep_mem t0) _ (mem_unitsModCoset.mp hu0)
        rwa [mul_inv_cancel_left] at this
      · intro t _ ht
        exact Set.indicator_of_notMem (fun h => ht (eq_of_mem_unitsModCoset h hu0)) _
      · intro h
        exact absurd (Finset.mem_univ t0) h
    · rw [Set.indicator_of_notMem hu]
      refine (Finset.sum_eq_zero fun t _ => Set.indicator_of_notMem ?_ _).symm
      exact fun h => hu (unitsModCoset_subset t h)
  have hint : ∀ t : unitsModFiltration K c,
      Integrable ((unitsModCoset t).indicator fun _ => G (unitsModRep t)) (multHaar K) := by
    intro t
    refine (integrable_indicator_iff (measurableSet_unitsModCoset t)).mpr (integrableOn_const ?_)
    rw [multHaar_unitsModCoset]
    exact (multHaar_unitFiltrationUnits_lt_top c).ne
  rw [← integral_indicator ((isOpen_unitFiltrationUnits 0).measurableSet), hcover,
    integral_finset_sum _ fun t _ => hint t]
  · simp only [integral_indicator_const _ (measurableSet_unitsModCoset _), measureReal_def,
      multHaar_unitsModCoset, Complex.real_smul]
    rw [Finset.mul_sum]

theorem multHaar_unitFiltrationUnits {c : ℕ} (hc : 1 ≤ c) :
    (multHaar K (unitFiltrationUnits K c)).toReal =
      (multHaarConst K).toReal * (haarIntegers K).real (valBall K c) := by
  classical
  have h := localZeta_oneAddValBallIndicator (χ := (1 : Kˣ →* ℂˣ)) hc
    (fun _ _ => MonoidHom.mem_ker.mpr rfl) 0
  have hpt : ∀ u : Kˣ, oneAddValBallIndicator (c : ℤ) (u : K) * (((1 : Kˣ →* ℂˣ) u : ℂˣ) : ℂ) *
      ((modulus (u : K) : ℝ) : ℂ) ^ (0 : ℂ) =
      (unitFiltrationUnits K c : Set Kˣ).indicator (fun _ => (1 : ℂ)) u := by
    intro u
    rw [oneAddValBallIndicator_apply, MonoidHom.one_apply, Units.val_one, Complex.cpow_zero,
      mul_one, mul_one]
    by_cases hu : (u : K) - 1 ∈ valBall K c
    · rw [if_pos hu, Set.indicator_of_mem ((mem_unitFiltrationUnits_iff_valBall hc).mpr hu)]
    · rw [if_neg hu, Set.indicator_of_notMem (mt (mem_unitFiltrationUnits_iff_valBall hc).mp hu)]
  unfold localZeta at h
  rw [show (fun u : Kˣ => oneAddValBallIndicator (c : ℤ) (u : K) *
      (((1 : Kˣ →* ℂˣ) u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ (0 : ℂ)) =
      fun u : Kˣ => (unitFiltrationUnits K c : Set Kˣ).indicator (fun _ => (1 : ℂ)) u from
      funext hpt,
    integral_indicator_const _ (isOpen_unitFiltrationUnits c).measurableSet, Complex.real_smul,
    mul_one, measureReal_def] at h
  exact_mod_cast h

end Integral

section Gauss

variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle}

variable (χ ψ) in

def gaussSum : ℂ :=
  ∑ t : unitsModFiltration K (quasiCharConductor χ),
    ((χ (unifUnit K ^ (addCharConductor ψ - quasiCharConductor χ) * unitsModRep t) : ℂˣ) : ℂ)⁻¹ *
      (ψ ((unifUnit K ^ (addCharConductor ψ - quasiCharConductor χ) * unitsModRep t : Kˣ) : K) : ℂ)

theorem gaussSum_term_mul_eq (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (hχ : Continuous χ)
    (hr : ¬ IsUnramifiedChar χ) {x w : Kˣ} (hx : x ∈ unitFiltrationUnits K 0)
    (hw : w ∈ unitFiltrationUnits K (quasiCharConductor χ)) :
    ((χ (unifUnit K ^ (addCharConductor ψ - quasiCharConductor χ) * (x * w)) : ℂˣ) : ℂ)⁻¹ *
        (ψ ((unifUnit K ^ (addCharConductor ψ - quasiCharConductor χ) * (x * w) : Kˣ) : K) : ℂ) =
      ((χ (unifUnit K ^ (addCharConductor ψ - quasiCharConductor χ) * x) : ℂˣ) : ℂ)⁻¹ *
        (ψ ((unifUnit K ^ (addCharConductor ψ - quasiCharConductor χ) * x : Kˣ) : K) : ℂ) := by
  set c := quasiCharConductor χ
  set n := addCharConductor ψ
  set m : ℤ := n - c with hm
  set π := unifUnit K
  have hc : 1 ≤ c := quasiCharConductor_pos hχ hr
  have hker := unitFiltrationUnits_quasiCharConductor_le_ker hχ hw
  have hx0 : ord (x : K) = 0 := mem_unitFiltrationUnits_zero_iff_ord.mp hx
  have hw1 : (w : K) - 1 ∈ valBall K c := (mem_unitFiltrationUnits_iff_valBall hc).mp hw
  have hψw : (ψ ((π ^ m * (x * w) : Kˣ) : K) : ℂ) = (ψ ((π ^ m * x : Kˣ) : K) : ℂ) := by
    have hmem : ((π ^ m * x : Kˣ) : K) * ((w : K) - 1) ∈ valBall K n := by
      have := mul_mem_valBall ((mem_valBall_iff_le_ord (π ^ m * x).ne_zero).mpr le_rfl) hw1
      rw [ord_units_mul, ord_unifUnit_zpow, hx0] at this
      simpa [hm] using this
    rw [show ((π ^ m * (x * w) : Kˣ) : K) = ((π ^ m * x : Kˣ) : K) +
        ((π ^ m * x : Kˣ) : K) * ((w : K) - 1) by push_cast; ring,
      AddChar.map_add_eq_mul, isTrivialOn_addCharConductor hψ hψ1 _ hmem, mul_one]
  rw [hψw, ← mul_assoc, map_mul (χ) (π ^ m * x) w, MonoidHom.mem_ker.mp hker, mul_one]

theorem localEpsilon_eq_gaussSum (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (hχ : Continuous χ)
    (hr : ¬ IsUnramifiedChar χ) (s : ℂ) :
    localEpsilon χ ψ s =
      (residueCard K : ℂ) ^ (((addCharConductor ψ - quasiCharConductor χ : ℤ) : ℂ) * s -
        (addCharConductor ψ : ℂ) / 2) * gaussSum χ ψ := by
  rw [localEpsilon_of_not_isUnramified_eq hr]
  set c := quasiCharConductor χ
  set n := addCharConductor ψ
  set m : ℤ := n - c with hm
  have hc : 1 ≤ c := quasiCharConductor_pos hχ hr
  set π := unifUnit K
  let F : Kˣ → ℂ := fun u => ((χ u : ℂˣ) : ℂ)⁻¹ * (ψ (u : K) : ℂ)

  have h1 : ∫ u in ordShell K m, F u ∂multHaar K =
      ∫ v in (unitFiltrationUnits K 0 : Set Kˣ), F (π ^ m * v) ∂multHaar K := by
    have := setIntegral_ordShell_mul F (π ^ m) 0
    rwa [ord_unifUnit_zpow, add_zero, ordShell_zero] at this

  have h2 : ∫ v in (unitFiltrationUnits K 0 : Set Kˣ), F (π ^ m * v) ∂multHaar K =
      ((multHaar K (unitFiltrationUnits K c)).toReal : ℂ) * gaussSum χ ψ := by
    exact setIntegral_units_eq_sum (fun v => F (π ^ m * v)) fun x hx w hw =>
      gaussSum_term_mul_eq hψ hψ1 hχ hr hx hw

  have h3 := setIntegral_ordShell_eq_haarIntegers (fun x => quasiCharExt χ⁻¹ x * (ψ x : ℂ)) m
  have hFe : (fun u : Kˣ => quasiCharExt χ⁻¹ (u : K) * (ψ (u : K) : ℂ)) = F := by
    funext u
    rw [quasiCharExt_units, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  simp only [hFe] at h3
  rw [h1, h2, multHaar_unitFiltrationUnits hc] at h3
  set A := ∫ x in (valBall K m : Set K) \ valBall K (m + 1), quasiCharExt χ⁻¹ x * (ψ x : ℂ)
    ∂haarIntegers K
  set C := (multHaarConst K).toReal
  have hC : (C : ℂ) ≠ 0 := by
    exact_mod_cast ENNReal.toReal_ne_zero.mpr ⟨multHaarConst_ne_zero, multHaarConst_ne_top⟩
  have hq := residueCard_ne_zero_complex (K := K)
  have hB : (haarIntegers K).real (valBall K c) = (residueCard K : ℝ) ^ (-(c : ℤ)) := by
    rw [measureReal_def, haarIntegers_valBall, ENNReal.coe_toReal, NNReal.coe_zpow,
      NNReal.coe_natCast]
  rw [hB] at h3
  push_cast at h3
  have hCq : (C : ℂ) * (residueCard K : ℂ) ^ m ≠ 0 := mul_ne_zero hC (zpow_ne_zero _ hq)
  refine mul_left_cancel₀ hCq ?_
  have e1 : (((residueCard K : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * (residueCard K : ℂ) ^ (-(c : ℤ)) =
      (residueCard K : ℂ) ^ m * (residueCard K : ℂ) ^ (-(n : ℂ) / 2) := by
    rw [ofReal_qrpow, ← Complex.cpow_intCast, ← Complex.cpow_intCast, qcpow_mul_qcpow,
      qcpow_mul_qcpow]
    congr 1
    rw [hm]
    push_cast
    ring
  have e2 : (residueCard K : ℂ) ^ ((m : ℂ) * s - (n : ℂ) / 2) =
      (residueCard K : ℂ) ^ ((m : ℂ) * s) * (residueCard K : ℂ) ^ (-(n : ℂ) / 2) := by
    rw [qcpow_mul_qcpow]
    congr 1
    ring
  rw [show (((n - c : ℤ)) : ℂ) = (m : ℂ) from rfl, e2]
  linear_combination (-((residueCard K : ℂ) ^ ((m : ℂ) * s) *
    (((residueCard K : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ))) * h3 +
    ((residueCard K : ℂ) ^ ((m : ℂ) * s) * (C : ℂ) * gaussSum χ ψ) * e1

end Gauss

end GroundTheory.LocalField
