import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbFnValueSpan
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace HilbFnValueSpan

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

def coneQ (y : (Σ k, ι k) → Ω) : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] MvPolynomial K Ω :=
  aeval fun p => MvPolynomial.C (y p) * MvPolynomial.X p.1

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem map_mCoordIdeal (y : (Σ k, ι k) → Ω) :
    (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) = RingHom.ker (coneQ y) := by
  have hring : ((coneQ y : MvPolynomial (Σ k, ι k) ℚ →+* MvPolynomial K Ω).comp
      (MvPolynomial.map (Int.castRingHom ℚ))) = (mConeMap y : MRing ι →+* MvPolynomial K Ω) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coneQ, mConeMap]
    · intro i
      simp [coneQ, mConeMap]
  have hker : mCoordIdeal y =
      (RingHom.ker (coneQ y)).comap (MvPolynomial.map (Int.castRingHom ℚ)) := by
    ext f
    rw [Ideal.mem_comap]
    simp only [mCoordIdeal, RingHom.mem_ker]
    have h := RingHom.congr_fun hring f
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe] at h
    rw [h]
  let _ := MvPolynomial.algebraMvPolynomial (σ := Σ k, ι k) (R := ℤ) (S := ℚ)
  have e : algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) =
      MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  have h := IsLocalization.map_under ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k)))
    (MvPolynomial (Σ k, ι k) ℚ) (RingHom.ker (coneQ y))
  rw [e] at h
  rw [hker]
  exact h

theorem weight_blockWeight (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (NumbersDVR.blockWeight ι) m k = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [NumbersDVR.blockWeight, Pi.single_apply]

theorem isWeightedHomogeneous_iff {R : Type} [CommRing R] (f : MvPolynomial (Σ k, ι k) R) (a : K → ℕ) :
    IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a ↔ ∀ m ∈ f.support, ∀ k, ∑ i, m ⟨k, i⟩ = a k := by
  constructor
  · intro h m hm k
    rw [← weight_blockWeight, h (mem_support_iff.mp hm)]
  · intro h m hm
    funext k
    rw [weight_blockWeight, h m (mem_support_iff.mpr hm) k]

theorem coneQ_eq (y : (Σ k, ι k) → Ω) {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) :
    coneQ y f = MvPolynomial.C (aeval y f) * ∏ k, MvPolynomial.X k ^ a k := by
  have hf' := (isWeightedHomogeneous_iff f a).mp hf
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ m p =
      ∏ k, MvPolynomial.X k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf' m hm k]
  simp only [coneQ, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring

theorem mem_ker_iff (y : (Σ k, ι k) → Ω) {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) :
    f ∈ RingHom.ker (coneQ y) ↔ aeval y f = 0 := by
  rw [RingHom.mem_ker, coneQ_eq y hf]
  constructor
  · intro h
    have hne : (∏ k, MvPolynomial.X k ^ a k : MvPolynomial K Ω) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k)
    rcases mul_eq_zero.mp h with h | h
    · exact MvPolynomial.C_eq_zero.mp h
    · exact absurd h hne
  · intro h
    rw [h, map_zero, zero_mul]

def evalForms (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι) a →ₗ[ℚ] Ω :=
  (aeval y : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω).toLinearMap.comp (Submodule.subtype _)

def quotForms (P : Ideal (MvPolynomial (Σ k, ι k) ℚ)) (a : K → ℕ) :
    weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι) a →ₗ[ℚ] MvPolynomial (Σ k, ι k) ℚ ⧸ P :=
  (Ideal.Quotient.mkₐ ℚ P).toLinearMap.comp (Submodule.subtype _)

theorem range_evalForms (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    LinearMap.range (evalForms y a) = valueSpan y a := by
  apply le_antisymm
  · rintro _ ⟨⟨f, hf⟩, rfl⟩
    have hf' := (isWeightedHomogeneous_iff f a).mp ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hf)
    show aeval y f ∈ valueSpan y a
    conv => arg 2; rw [f.as_sum]
    rw [map_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    have hmon : aeval y (monomial v (coeff v f)) =
        coeff v f • aeval y (monomial v (1 : ℤ) : MRing ι) := by
      simp only [aeval_monomial, Algebra.smul_def, map_one, one_mul]
    rw [hmon]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨monomial v 1, ?_, rfl⟩)
    intro m hm k
    rw [support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hm
    rw [hm]
    exact hf' v hv k
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    have hmem : MvPolynomial.map (Int.castRingHom ℚ) g ∈
        weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι) a := by
      rw [mem_weightedHomogeneousSubmodule, isWeightedHomogeneous_iff]
      exact fun m hm k => hg m (support_map_subset _ _ hm) k
    refine ⟨⟨_, hmem⟩, ?_⟩
    show aeval y (MvPolynomial.map (Int.castRingHom ℚ) g) = aeval y g
    rw [← algebraMap_int_eq, aeval_map_algebraMap]

theorem finrank_gradedPiece (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    Module.finrank ℚ (NumbersDVR.gradedPiece
        ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))) a) =
      Module.finrank ℚ (valueSpan y a) := by
  set P := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))
  have hrange : LinearMap.range (quotForms P a) = NumbersDVR.gradedPiece P a := by
    rw [quotForms, LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hker : LinearMap.ker (quotForms P a) = LinearMap.ker (evalForms y a) := by
    ext ⟨f, hf⟩
    rw [mem_weightedHomogeneousSubmodule] at hf
    simp only [LinearMap.mem_ker, quotForms, evalForms, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    rw [show P = RingHom.ker (coneQ y) from map_mCoordIdeal y, mem_ker_iff y hf]
  rw [← hrange, ← range_evalForms y a, ← (quotForms P a).quotKerEquivRange.finrank_eq,
    ← (evalForms y a).quotKerEquivRange.finrank_eq]
  exact (Submodule.quotEquivOfEq _ _ hker).finrank_eq

end HilbFnValueSpan

theorem HilbFnValueSpan.proof : HilbFnValueSpan.Statement := by
  intro K _ _ ι _ Ω _ _ y a
  unfold NumbersDVR.hilbFn
  rw [if_pos (fun k => Int.natCast_nonneg _)]
  have ha : (fun k => ((a k : ℤ)).toNat) = a := funext fun k => Int.toNat_natCast _
  rw [ha, HilbFnValueSpan.finrank_gradedPiece]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
