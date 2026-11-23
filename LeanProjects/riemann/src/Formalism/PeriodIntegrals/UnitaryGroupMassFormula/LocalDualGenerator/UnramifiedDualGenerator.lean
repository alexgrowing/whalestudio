import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.FpDualUnram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.IsClosedO
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemOfClosed

noncomputable section

open ValuativeRel IsLocalRing

namespace PI.LocDualGen.FpU

theorem exists_trace_ne_zero (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
    [Algebra (ZMod p) F] : ∃ z : F, Algebra.trace (ZMod p) F z ≠ 0 := by
  have h : ringChar F = p := ringChar.eq F p
  subst h
  obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate F (one_ne_zero : (1 : F) ≠ 0)
  exact ⟨b, by simpa using hb⟩

section Main

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K]

variable [CharP 𝓀[K] l]

attribute [local instance] algRes

theorem linIndep (hcont : Continuous (algebraMap ℚ_[l] K)) :
    LinearIndependent ℚ_[l] (fun i => (blift K l i : K)) :=
  by apply _root_.UpperTheory.Reformulated.B.Qi13.linIndep <;> assumption

theorem exists_pow_mul_mem (huni : Irreducible ((l : ℕ) : 𝒪[K])) (x : K) :
    ∃ n : ℕ, (l : K) ^ n * x ∈ 𝒪[K] := by
  by_cases hx : x ∈ 𝒪[K]
  · exact ⟨0, by simpa using hx⟩
  have hx1 : 1 < valuation K x := by
    rw [Valuation.mem_integer_iff, not_le] at hx
    exact hx
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx1
    exact absurd hx1 (not_lt.mpr zero_le)
  have hinv : x⁻¹ ∈ 𝒪[K] := by
    rw [Valuation.mem_integer_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ hx1.le
  have hr0 : (⟨x⁻¹, hinv⟩ : 𝒪[K]) ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    exact inv_ne_zero hx0 this
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 huni
  refine ⟨n, ?_⟩
  have hu' : x⁻¹ = ((u : 𝒪[K]) : K) * (l : K) ^ n := by
    have := congrArg Subtype.val hu
    simpa using this
  have huu : ((u : 𝒪[K]) : K) * (((u⁻¹ : (𝒪[K])ˣ) : 𝒪[K]) : K) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv]
    rfl
  have hxe : x = (((u : 𝒪[K]) : K) * (l : K) ^ n)⁻¹ := by rw [← hu', inv_inv]
  have hl0 : ((l : K)) ^ n ≠ 0 := by
    intro h
    rw [h, mul_zero] at hu'
    exact inv_ne_zero hx0 hu'
  have hv : (l : K) ^ n * x = (((u⁻¹ : (𝒪[K])ˣ) : 𝒪[K]) : K) := by
    rw [hxe, mul_inv, ← mul_assoc, mul_comm ((l : K) ^ n), mul_assoc, mul_inv_cancel₀ hl0, mul_one]
    exact inv_eq_of_mul_eq_one_right huu
  rw [hv]
  exact (u⁻¹ : (𝒪[K])ˣ).1.2

theorem spanTop (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K])) :
    ⊤ ≤ Submodule.span ℚ_[l] (Set.range fun i => (blift K l i : K)) := by
  intro x _
  obtain ⟨n, hn⟩ := exists_pow_mul_mem K l huni x
  obtain ⟨c, hc⟩ := span K l hcont huni ⟨_, hn⟩
  have hc' := congrArg Subtype.val hc
  rw [Phi_coe] at hc'
  change (l : K) ^ n * x = _ at hc'
  have hl0 : (l : K) ^ n ≠ 0 := pow_ne_zero _ (by
    rw [← map_natCast (algebraMap ℚ_[l] K)]
    exact (map_ne_zero _).mpr (by exact_mod_cast (Fact.out : l.Prime).ne_zero))
  have hx : x = ∑ i, (((l : ℚ_[l]) ^ n)⁻¹ * (c i : ℚ_[l])) • (blift K l i : K) := by
    have e : x = ((l : K) ^ n)⁻¹ * ((l : K) ^ n * x) := by field_simp
    rw [e, hc', Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Algebra.smul_def, map_mul, map_inv₀, map_pow, map_natCast]
    ring
  rw [hx]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

def B (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K])) :
    Module.Basis (Fin (fdim K l)) ℚ_[l] K :=
  Module.Basis.mk (linIndep K l hcont) (spanTop K l hcont huni)

theorem B_apply (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (i : Fin (fdim K l)) : B K l hcont huni i = (blift K l i : K) := by
  simp [B]

def coef (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (y : 𝒪[K]) : Fin (fdim K l) → ℤ_[l] :=
  (span K l hcont huni y).choose

theorem repr_coe (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (y : 𝒪[K]) (j : Fin (fdim K l)) :
    (B K l hcont huni).repr (y : K) j = (coef K l hcont huni y j : ℚ_[l]) := by
  have h' : (y : K) = ((Phi K l hcont (coef K l hcont huni y) : 𝒪[K]) : K) :=
    congrArg Subtype.val (span K l hcont huni y).choose_spec
  rw [h', Phi_coe]
  have e : ∑ i, algebraMap ℚ_[l] K ((coef K l hcont huni y i : ℤ_[l]) : ℚ_[l]) * (blift K l i : K) =
      ∑ i, ((coef K l hcont huni y i : ℤ_[l]) : ℚ_[l]) • B K l hcont huni i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [B_apply, Algebra.smul_def]
  rw [e, repr_sum]

theorem res_coef (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (y : 𝒪[K]) (j : Fin (fdim K l)) :
    (bb K l).repr (residue 𝒪[K] y) j = PadicInt.toZMod (coef K l hcont huni y j) := by
  conv_lhs => rw [(span K l hcont huni y).choose_spec]
  rw [res_Phi, repr_sum]
  rfl

theorem trace_eq (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (x : 𝒪[K]) : Algebra.trace ℚ_[l] K (x : K) =
      ((∑ i, coef K l hcont huni (x * blift K l i) i : ℤ_[l]) : ℚ_[l]) := by
  rw [Algebra.trace_eq_matrix_trace (B K l hcont huni), Matrix.trace]
  rw [show ((∑ i, coef K l hcont huni (x * blift K l i) i : ℤ_[l]) : ℚ_[l]) =
      ∑ i, ((coef K l hcont huni (x * blift K l i) i : ℤ_[l]) : ℚ_[l]) from
    map_sum PadicInt.Coe.ringHom _ _]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, B_apply]
  have e : (x : K) * (blift K l i : K) = ((x * blift K l i : 𝒪[K]) : K) := rfl
  rw [e, repr_coe]

theorem toZMod_trace (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (x : 𝒪[K]) : PadicInt.toZMod (∑ i, coef K l hcont huni (x * blift K l i) i) =
      Algebra.trace (ZMod l) 𝓀[K] (residue 𝒪[K] x) := by
  rw [Algebra.trace_eq_matrix_trace (bb K l), Matrix.trace, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, ← res_blift K l i, ← map_mul, res_coef]

theorem trace_int (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (x : 𝒪[K]) : ‖Algebra.trace ℚ_[l] K (x : K)‖ ≤ 1 := by
  rw [trace_eq K l hcont huni]
  exact (∑ i, coef K l hcont huni (x * blift K l i) i).2

theorem exists_trace_unit (hcont : Continuous (algebraMap ℚ_[l] K))
    (huni : Irreducible ((l : ℕ) : 𝒪[K])) : ∃ x : 𝒪[K], ¬ ‖Algebra.trace ℚ_[l] K (x : K)‖ < 1 := by
  obtain ⟨z, hz⟩ := exists_trace_ne_zero 𝓀[K] l
  obtain ⟨x, rfl⟩ := residue_surjective z
  refine ⟨x, fun hlt => hz ?_⟩
  rw [← toZMod_trace K l hcont huni]
  rw [trace_eq K l hcont huni] at hlt
  have hnu : (∑ i, coef K l hcont huni (x * blift K l i) i) ∈ maximalIdeal ℤ_[l] :=
    (mem_maximalIdeal _).mpr (PadicInt.mem_nonunits.mpr hlt)
  rw [← PadicInt.ker_toZMod] at hnu
  exact hnu

end Main

theorem unramified_dual_generator : PI.LocDualGen.W.FpDualUnram := by
  intro K _ _ _ l _ _ hlf _ hcont _ huni a
  haveI := hlf
  haveI := charP_res K l huni
  letI := algRes K l
  obtain ⟨z, hz⟩ := exists_trace_unit K l hcont huni
  constructor
  · intro H
    by_contra ha
    have ha1 : 1 < valuation K a := by
      rw [Valuation.mem_integer_iff, not_le] at ha
      exact ha
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, map_zero] at ha1
      exact absurd ha1 (not_lt.mpr zero_le)
    have hinv : a⁻¹ ∈ 𝒪[K] := by
      rw [Valuation.mem_integer_iff, map_inv₀]
      exact inv_le_one_of_one_le₀ ha1.le
    have hnu : (⟨a⁻¹, hinv⟩ : 𝒪[K]) ∈ maximalIdeal 𝒪[K] := by
      rw [mem_maximalIdeal, mem_nonunits_iff,
        (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one]
      intro h1
      change valuation K a⁻¹ = 1 at h1
      rw [map_inv₀, inv_eq_one] at h1
      rw [h1] at ha1
      exact lt_irrefl _ ha1
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp huni,
      Ideal.mem_span_singleton'] at hnu
    obtain ⟨t, ht⟩ := hnu
    have ht' : (t : K) * (l : K) = a⁻¹ := congrArg Subtype.val ht
    have hl0 : (l : K) ≠ 0 := by
      rw [← map_natCast (algebraMap ℚ_[l] K)]
      exact (map_ne_zero _).mpr (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
    have hat : a * (t : K) = algebraMap ℚ_[l] K ((l : ℚ_[l])⁻¹) := by
      rw [map_inv₀, map_natCast]
      field_simp
      have := congrArg (fun w => a * w) ht'
      simp only [mul_inv_cancel₀ ha0] at this
      rw [← this]
      ring
    have h1 := H (t * z)
    change ‖Algebra.trace ℚ_[l] K (a * ((t : K) * (z : K)))‖ ≤ 1 at h1
    rw [← mul_assoc, hat, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, norm_mul, norm_inv] at h1
    have hlpos : 0 < ‖(l : ℚ_[l])‖ := norm_pos_iff.mpr (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
    rw [inv_mul_le_iff₀ hlpos, mul_one] at h1
    exact hz (lt_of_le_of_lt h1 Padic.norm_p_lt_one)
  · intro ha b
    exact trace_int K l hcont huni ⟨a * b, mul_mem ha b.2⟩

end PI.LocDualGen.FpU
