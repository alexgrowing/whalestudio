import Formalism.HermitianCurvature.LatticeHerglotzBound

open MeasureTheory Set Polynomial

noncomputable section

namespace Formalism.FourierDecayAlt.P.NthRootMeasurability

open Formalism.FourierDecayAlt.crystallineComparison

theorem detC (d : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ).det = ‖d‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq,
    Complex.normSq_eq_norm_sq]

def zeta (s : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / s)

def R (s k : ℕ) (w : ℂ) : ℂ := zeta s ^ k * w ^ ((s : ℂ)⁻¹)

def A (s k : ℕ) : Set ℂ := {z | z ≠ 0 ∧ R s k (z ^ s) = z}

theorem measurable_R (s k : ℕ) : Measurable (R s k) := by
  unfold R; fun_prop

theorem measurableSet_A (s k : ℕ) : MeasurableSet (A s k) := by
  have h1 : MeasurableSet {z : ℂ | z ≠ 0} := (measurableSet_singleton (0 : ℂ)).compl
  have h2 : MeasurableSet {z : ℂ | R s k (z ^ s) = z} :=
    measurableSet_eq_fun ((measurable_R s k).comp (by fun_prop)) measurable_id
  exact h1.inter h2

theorem R_pow (s k : ℕ) (hs : s ≠ 0) (w : ℂ) : R s k w ^ s = w := by
  unfold R zeta
  rw [mul_pow, ← pow_mul, mul_comm k s, pow_mul, (Complex.isPrimitiveRoot_exp s hs).pow_eq_one,
    one_pow, one_mul, Complex.cpow_nat_inv_pow w hs]

theorem nthRoots_eq_R (s : ℕ) (hs : s ≠ 0) (w : ℂ) :
    nthRoots s w = (Multiset.range s).map (fun k => R s k w) :=
  (Complex.isPrimitiveRoot_exp s hs).nthRoots_eq (Complex.cpow_nat_inv_pow w hs)

theorem sum_roots (s : ℕ) (hs : s ≠ 0) (H : ℂ → ENNReal) (w : ℂ) :
    ((nthRoots s w).map H).sum = ∑ k ∈ Finset.range s, H (R s k w) := by
  rw [nthRoots_eq_R s hs, Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

theorem A_disjoint (s : ℕ) (hs : s ≠ 0) :
    Set.PairwiseDisjoint (↑(Finset.range s) : Set ℕ) (A s) := by
  intro j hj k hk hjk
  rw [Function.onFun, Set.disjoint_left]
  intro z hzj hzk
  apply hjk
  simp only [Finset.coe_range, Set.mem_Iio] at hj hk
  have e : zeta s ^ j * (z ^ s) ^ ((s : ℂ)⁻¹) = zeta s ^ k * (z ^ s) ^ ((s : ℂ)⁻¹) := by
    have := hzj.2.trans hzk.2.symm
    simpa [R] using this
  have hα : (z ^ s) ^ ((s : ℂ)⁻¹) ≠ 0 := by
    intro h0
    have := hzj.2
    simp only [R, h0, mul_zero] at this
    exact hzj.1 this.symm
  exact (Complex.isPrimitiveRoot_exp s hs).pow_inj hj hk (mul_right_cancel₀ hα e)

theorem A_union (s : ℕ) (hs : s ≠ 0) : (⋃ k ∈ Finset.range s, A s k) = {0}ᶜ := by
  ext z
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff, A,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, _, hz, _⟩; exact hz
  · intro hz
    have hmem : z ∈ nthRoots s (z ^ s) := (mem_nthRoots (Nat.pos_of_ne_zero hs)).mpr rfl
    rw [nthRoots_eq_R s hs, Multiset.mem_map] at hmem
    obtain ⟨k, hk, hkz⟩ := hmem
    exact ⟨k, Multiset.mem_range.mp hk, hz, hkz⟩

theorem image_A (s k : ℕ) (hs : s ≠ 0) (u : ℂ) (hu : u ≠ 0) :
    (fun z => u⁻¹ * z ^ s) '' A s k = {0}ᶜ := by
  ext c
  simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, A, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, ⟨hz, _⟩, rfl⟩
    exact mul_ne_zero (inv_ne_zero hu) (pow_ne_zero _ hz)
  · intro hc
    refine ⟨R s k (u * c), ⟨?_, ?_⟩, ?_⟩
    · intro h0
      have := R_pow s k hs (u * c)
      rw [h0, zero_pow hs] at this
      exact mul_ne_zero hu hc this.symm
    · rw [R_pow s k hs]
    · rw [R_pow s k hs, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]

theorem injOn_A (s k : ℕ) (u : ℂ) (hu : u ≠ 0) : InjOn (fun z => u⁻¹ * z ^ s) (A s k) := by
  intro z hz z' hz' e
  have e' : z ^ s = z' ^ s := mul_left_cancel₀ (inv_ne_zero hu) e
  rw [← hz.2, ← hz'.2, e']

theorem core (s : ℕ) (hs : s ≠ 0) (u : ℂ) (hu : u ≠ 0) (H : ℂ → ENNReal) (hH : Measurable H) :
    ∫⁻ c, ((nthRoots s (u * c)).map H).sum =
      ∫⁻ z, ENNReal.ofReal (‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2) * H z := by
  simp_rw [sum_roots s hs H]
  rw [lintegral_finsetSum (Finset.range s) (f := fun k c => H (R s k (u * c)))
    (fun k _ => hH.comp ((measurable_R s k).comp (measurable_const_mul u)))]
  have step : ∀ k, ∫⁻ c, H (R s k (u * c)) =
      ∫⁻ z in A s k, ENNReal.ofReal (‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2) * H z := by
    intro k
    calc ∫⁻ c, H (R s k (u * c)) = ∫⁻ c in {0}ᶜ, H (R s k (u * c)) := by
          rw [MeasureTheory.restrict_compl_singleton]
      _ = ∫⁻ c in (fun z => u⁻¹ * z ^ s) '' A s k, H (R s k (u * c)) := by
          rw [image_A s k hs u hu]
      _ = ∫⁻ z in A s k, ENNReal.ofReal |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
            (u⁻¹ * (s * z ^ (s - 1)))).restrictScalars ℝ).det| *
            H (R s k (u * (u⁻¹ * z ^ s))) :=
          lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (measurableSet_A s k)
            (fun z _ => (((hasDerivAt_pow s z).const_mul u⁻¹).hasFDerivAt.restrictScalars
              ℝ).hasFDerivWithinAt) (injOn_A s k u hu) _
      _ = _ := by
          refine setLIntegral_congr_fun (measurableSet_A s k) (fun z hz => ?_)
          rw [detC, abs_of_nonneg (sq_nonneg _), ← mul_assoc (u) u⁻¹, mul_inv_cancel₀ hu, one_mul,
            hz.2]
  simp_rw [step]
  rw [← lintegral_biUnion_finset (A_disjoint s hs) (fun k _ => measurableSet_A s k), A_union s hs,
    MeasureTheory.restrict_compl_singleton]

theorem real_id (s M : ℕ) (hs : 1 ≤ s) (hM : 2 ≤ M) (t z : ℂ) (ht : t ≠ 0) (hz : z ≠ 0) :
    ‖((-1 : ℂ) ^ (s + 1) * t ^ (s - 1))⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 *
      (‖t‖ ^ (2 * (s - 1) * (M + s - 2)) *
        ‖((-1 : ℂ) ^ (s + 1) * t ^ (s - 1))⁻¹ * z ^ s‖ ^ (2 * (M - 2)) /
          (‖t‖ ^ (2 * (s - 1) ^ 2) * (s : ℝ) ^ 2)) * ‖z‖ ^ (2 * (s - 1) ^ 2) =
      ‖z‖ ^ (2 * s * (M + s - 3)) := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 2 := ⟨M - 2, by omega⟩
  rw [show s' + 1 - 1 = s' by omega, show M' + 2 + (s' + 1) - 2 = M' + s' + 1 by omega,
    show M' + 2 - 2 = M' by omega, show M' + 2 + (s' + 1) - 3 = M' + s' by omega]
  simp only [norm_mul, norm_inv, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast]
  have hT : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hR : 0 < ‖z‖ := norm_pos_iff.mpr hz
  generalize ‖t‖ = T at hT ⊢
  generalize ‖z‖ = ρ at hR ⊢
  push_cast
  simp only [inv_pow, mul_pow, ← pow_mul]
  field_simp
  ring

theorem densityChange_ok : DensityChange := by
  intro s M t g hs hM ht hg
  have hs0 : s ≠ 0 := by omega
  have hu : ((-1 : ℂ) ^ (s + 1) * t ^ (s - 1)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ ht)
  calc _ = ∫⁻ c, ((nthRoots s (((-1 : ℂ) ^ (s + 1) * t ^ (s - 1)) * c)).map
            (fun z => ENNReal.ofReal (‖t‖ ^ (2 * (s - 1) * (M + s - 2)) *
              ‖((-1 : ℂ) ^ (s + 1) * t ^ (s - 1))⁻¹ * z ^ s‖ ^ (2 * (M - 2)) /
                (‖t‖ ^ (2 * (s - 1) ^ 2) * (s : ℝ) ^ 2)) *
              (ENNReal.ofReal (‖z‖ ^ (2 * (s - 1) ^ 2)) * g z))).sum := by
        refine lintegral_congr (fun c => ?_)
        rw [show (-1 : ℂ) ^ (s + 1) * (c * t ^ (s - 1)) = ((-1 : ℂ) ^ (s + 1) * t ^ (s - 1)) * c by
          ring, ← Multiset.sum_map_mul_left]
        congr 1
        refine Multiset.map_congr rfl (fun z hz => ?_)
        rw [mem_nthRoots (by omega)] at hz
        rw [hz, inv_mul_cancel_left₀ hu]
    _ = ∫⁻ z, ENNReal.ofReal (‖((-1 : ℂ) ^ (s + 1) * t ^ (s - 1))⁻¹ * (s * z ^ (s - 1))‖ ^ 2) *
            (ENNReal.ofReal (‖t‖ ^ (2 * (s - 1) * (M + s - 2)) *
              ‖((-1 : ℂ) ^ (s + 1) * t ^ (s - 1))⁻¹ * z ^ s‖ ^ (2 * (M - 2)) /
                (‖t‖ ^ (2 * (s - 1) ^ 2) * (s : ℝ) ^ 2)) *
              (ENNReal.ofReal (‖z‖ ^ (2 * (s - 1) ^ 2)) * g z)) :=
        core s hs0 _ hu _ (by
          refine (Measurable.ennreal_ofReal (by fun_prop)).mul
            ((Measurable.ennreal_ofReal (by fun_prop)).mul hg))
    _ = _ := by
        refine lintegral_congr_ae ?_
        filter_upwards [Measure.ae_ne volume (0 : ℂ)] with z hz
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), real_id s M hs hM t z ht hz]

end Formalism.FourierDecayAlt.P.NthRootMeasurability

theorem Formalism.FourierDecayAlt.P.rootPushforwardDensity : Formalism.FourierDecayAlt.crystallineComparison.DensityChange :=
  Formalism.FourierDecayAlt.P.NthRootMeasurability.densityChange_ok
