import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobalHaar
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteAdelicHaar

open MeasureTheory Measure Topology Filter Set IsDedekindDomain NumberField

namespace GroundTheory.Automorphic

namespace AutomorphicForm

noncomputable section

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

theorem isMulRightInvariant_infinite [MeasurableSpace (AdelicGLn.InfiniteAdelicGL K n)]
    [BorelSpace (AdelicGLn.InfiniteAdelicGL K n)] (μi : Measure (AdelicGLn.InfiniteAdelicGL K n))
    [μi.IsHaarMeasure] : μi.IsMulRightInvariant := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (AdelicGLn.InfiniteAdelicGL K 0) :=
      ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
    refine ⟨fun g => ?_⟩
    rw [Subsingleton.elim g 1]
    simp only [mul_one]
    exact Measure.map_id
  set μf : Measure (AdelicGLn.FiniteAdelicGL K n) := Measure.haar
  set P := μi.prod μf
  set e := AdelicGLn.prodEquiv K n
  set ν : Measure (AdelicGLn.AdelicGL K n) := Measure.haar
  have hν := GJGlobal.isMulRightInvariant_haar ν hn
  have he : Measurable e := e.continuous.measurable
  have : (ν.map e).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map ν e.toMulEquiv e.continuous e.symm.continuous
  have hν' : ∀ p, (ν.map e).map (· * p) = ν.map e := by
    intro p
    have hcomp : (· * p) ∘ e = e ∘ (· * e.symm p) := by
      funext x
      simp only [Function.comp_apply, map_mul, ContinuousMulEquiv.apply_symm_apply]
    rw [Measure.map_map (measurable_mul_const p) he, hcomp,
      ← Measure.map_map he (measurable_mul_const _), map_mul_right_eq_self]
  set c := haarScalarFactor (ν.map e) P
  have hc : ν.map e = c • P := isMulLeftInvariant_eq_smul (ν.map e) P
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    have hne := isOpen_univ.measure_ne_zero (ν.map e) univ_nonempty
    rw [hc] at hne
    exact hne rfl
  have hP : ∀ p, P.map (· * p) = P := by
    intro p
    have h1 : P = c⁻¹ • ν.map e := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [h1, Measure.map_smul, hν']
  refine ⟨fun g => ?_⟩
  have hprod : P.map (· * (g, (1 : AdelicGLn.FiniteAdelicGL K n))) = (μi.map (· * g)).prod μf := by
    have hf : (· * (g, (1 : AdelicGLn.FiniteAdelicGL K n))) = Prod.map (· * g) id := by
      funext p
      exact Prod.ext rfl (mul_one p.2)
    rw [hf, ← Measure.map_prod_map μi μf (measurable_mul_const g) measurable_id, Measure.map_id]
  rw [hP] at hprod
  obtain ⟨B, hBc, hB⟩ := exists_compact_mem_nhds (1 : AdelicGLn.FiniteAdelicGL K n)
  have hB0 : μf B ≠ 0 := (measure_pos_of_mem_nhds μf hB).ne'
  have hBt : μf B ≠ ⊤ := hBc.measure_lt_top.ne
  refine Measure.ext fun A hA => ?_
  have h1 := congrArg (fun m : Measure _ => m (A ×ˢ B)) hprod
  simp only [P, Measure.prod_prod] at h1
  exact ((ENNReal.mul_left_inj hB0 hBt).1 h1).symm

variable {K n}

theorem isMulRightInvariant_archGroup (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] :
    ν.IsMulRightInvariant := by
  let _ : MeasurableSpace (AdelicGLn.InfiniteAdelicGL K n) := _root_.borel _
  have : BorelSpace (AdelicGLn.InfiniteAdelicGL K n) := ⟨rfl⟩
  set φ := archEquiv K n
  have hφ : Measurable φ := φ.continuous.measurable
  have hφs : Measurable φ.symm := φ.symm.continuous.measurable
  set μi := ν.map φ.symm
  have : μi.IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map ν φ.symm.toMulEquiv φ.symm.continuous φ.continuous
  have hμi := isMulRightInvariant_infinite K n μi
  have hν : ν = μi.map φ := by
    rw [Measure.map_map hφ hφs]
    have : (φ ∘ φ.symm : archGroup K n → archGroup K n) = id := funext fun x => φ.apply_symm_apply x
    rw [this, Measure.map_id]
  refine ⟨fun g => ?_⟩
  rw [hν, Measure.map_map (measurable_mul_const g) hφ]
  have hcomp : (· * g) ∘ φ = φ ∘ (· * φ.symm g) := by
    funext x
    simp only [Function.comp_apply, map_mul, ContinuousMulEquiv.apply_symm_apply]
  rw [hcomp, ← Measure.map_map hφ (measurable_mul_const _), map_mul_right_eq_self]

theorem isInvInvariant_archGroup (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] :
    ν.IsInvInvariant := by
  have := isMulRightInvariant_archGroup ν
  have := secondCountableTopology_subgroup_units (archGroup K n)
  have := (isExpLieAlgebra K n).locallyCompactSpace
  constructor
  let c : ENNReal := Measure.haarScalarFactor ν.inv ν
  have hc : ν.inv = c • ν := Measure.isMulLeftInvariant_eq_smul ν.inv ν
  have h2 : Measure.map Inv.inv (Measure.map Inv.inv ν) = c ^ 2 • ν := by
    rw [← Measure.inv_def ν, hc, Measure.map_smul, ← Measure.inv_def ν, hc, smul_smul, pow_two]
  have νeq : ν = c ^ 2 • ν := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h2
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h2
  have Kc : TopologicalSpace.PositiveCompacts (archGroup K n) := Classical.arbitrary _
  have h3 : c ^ 2 * ν Kc = 1 ^ 2 * ν Kc := by
    conv_rhs => rw [νeq]
    simp
  have h4 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (measure_pos_of_nonempty_interior _ Kc.interior_nonempty).ne'
      Kc.isCompact.measure_lt_top.ne).1 h3
  have h5 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h4
  rw [hc, h5, one_smul]

theorem integral_inv_archGroup (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : archGroup K n → E) :
    ∫ a, f a⁻¹ ∂ν = ∫ a, f a ∂ν := by
  have := isInvInvariant_archGroup ν
  exact integral_inv_eq_self f ν

theorem integral_conj_archGroup (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : archGroup K n → E) (k : archGroup K n) :
    ∫ a, f (k * a * k⁻¹) ∂ν = ∫ a, f a ∂ν := by
  have := isMulRightInvariant_archGroup ν
  simp_rw [mul_assoc]
  rw [integral_mul_right_eq_self (fun a => f (k * a)) k⁻¹, integral_mul_left_eq_self]

end

end AutomorphicForm

end GroundTheory.Automorphic
