import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.HalfPeriodStandardCM
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.IsTorsionPointStandardCM
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.DetMemOfEntries
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobalLUnit

noncomputable section
open scoped ComplexConjugate

namespace GlobalTheory.TraceNormCoordinates

theorem exists_coords (b : ℤ) (d : ℕ) (hd : 0 < d) {x : ℂ} (hx : x ∈ PI.UnitaryGroupMassFormula.UnitDetRoot.KF b d) :
    ∃ p q : ℚ, x = (p : ℂ) + (q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) := by
  set s : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ) with hs_def
  have hs : s * s = -(d : ℂ) := by
    have h2 : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = (d : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
      simp
    calc s * s = (Complex.I * Complex.I) * (((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ)) := by
          rw [hs_def]; ring
      _ = -(d : ℂ) := by rw [Complex.I_mul_I, h2]; ring
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨(b : ℚ) / 2, 1 / 2, ?_⟩
    simp only [PI.UnitDetRootDefs.cmTheta, hs_def]
    push_cast
    ring
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨p, q, rfl⟩ := ihx
    obtain ⟨p', q', rfl⟩ := ihy
    exact ⟨p + p', q + q', by push_cast; ring⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨p, q, rfl⟩ := ihx
    obtain ⟨p', q', rfl⟩ := ihy
    refine ⟨p * p' - d * q * q', p * q' + q * p', ?_⟩
    push_cast
    linear_combination (q : ℂ) * q' * hs
  | inv x _ ih =>
    obtain ⟨p, q, rfl⟩ := ih
    by_cases h0 : p = 0 ∧ q = 0
    · obtain ⟨rfl, rfl⟩ := h0
      exact ⟨0, 0, by simp⟩
    · have hN : p ^ 2 + d * q ^ 2 ≠ 0 := by
        intro hz
        apply h0
        have h1 : p ^ 2 = 0 := by nlinarith [sq_nonneg p, mul_nonneg hdq.le (sq_nonneg q)]
        have h2 : q ^ 2 = 0 := by nlinarith [sq_nonneg p, sq_nonneg q, mul_nonneg hdq.le (sq_nonneg q)]
        exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1, pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2⟩
      have hNc : ((p : ℂ) ^ 2 + (d : ℂ) * (q : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hN
      refine ⟨p / (p ^ 2 + d * q ^ 2), -q / (p ^ 2 + d * q ^ 2), ?_⟩
      apply inv_eq_of_mul_eq_one_right
      clear_value s
      have e : ((p : ℂ) + q * s) * (((p / (p ^ 2 + d * q ^ 2) : ℚ) : ℂ) + ((-q / (p ^ 2 + d * q ^ 2) : ℚ) : ℂ) * s)
          = ((p : ℂ) ^ 2 - (q : ℂ) ^ 2 * (s * s)) / ((p : ℂ) ^ 2 + (d : ℂ) * (q : ℂ) ^ 2) := by
        push_cast
        ring
      rw [e, hs, div_eq_one_iff_eq hNc]
      ring

theorem norm_le_one_of_trace {F : Type*} [NormedField F] [IsUltrametricDist F] {y y' : F}
    (h : y * y' = 1) (ht : ‖y + y'‖ ≤ 1) : ‖y‖ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have hn : ‖y‖ * ‖y'‖ = 1 := by rw [← norm_mul, h, norm_one]
  have hy' : ‖y'‖ < ‖y‖ := by nlinarith [norm_nonneg y', norm_nonneg y]
  have hmax := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hy')
  rw [hmax, max_eq_left hy'.le] at ht
  linarith

theorem norm_eq_one {a : ℕ} {b c : ℤ} {d : ℕ} (hok : PI.UnitDetRootDefs.CmOK a b c d) (l : ℕ)
    [inst : Fact (Nat.Prime l)]
    (hT : ∀ T v : ℚ_[l], T ^ 2 + (d : ℚ_[l]) * v ^ 2 = 4 → ‖T‖ ≤ 1)
    (ι : ℂ ≃+* ℂ_[l]) {x : ℂ} (hx : x ∈ PI.UnitaryGroupMassFormula.UnitDetRoot.KF b d) (h1 : x * conj x = 1) :
    ‖ι x‖ = 1 := by
  have hd : 0 < d := hok.2.2.2.pos
  obtain ⟨p, q, rfl⟩ := exists_coords b d hd hx
  set s : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ) with hs_def
  have hs : s * s = -(d : ℂ) := by
    have h2 : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = (d : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
      simp
    calc s * s = (Complex.I * Complex.I) * (((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ)) := by
          rw [hs_def]; ring
      _ = -(d : ℂ) := by rw [Complex.I_mul_I, h2]; ring
  have hcs : conj s = -s := by simp [hs_def]
  have hconj : conj ((p : ℂ) + (q : ℂ) * s) = (p : ℂ) - (q : ℂ) * s := by
    rw [map_add, map_mul, hcs, map_ratCast, map_ratCast]; ring
  rw [hconj] at h1

  have hpq : (p ^ 2 + d * q ^ 2 : ℚ) = 1 := by
    have : (((p ^ 2 + d * q ^ 2 : ℚ)) : ℂ) = 1 := by
      push_cast
      linear_combination h1 + (q : ℂ) ^ 2 * hs
    exact_mod_cast this
  have hT' : ‖((2 * p : ℚ) : ℚ_[l])‖ ≤ 1 := by
    apply hT _ ((2 * q : ℚ) : ℚ_[l])
    have : ((2 * p) ^ 2 + d * (2 * q) ^ 2 : ℚ) = 4 := by linear_combination 4 * hpq
    exact_mod_cast congrArg (fun r : ℚ => (r : ℚ_[l])) this
  set y := ι ((p : ℂ) + (q : ℂ) * s)
  set y' := ι ((p : ℂ) - (q : ℂ) * s)
  have hyy : y * y' = 1 := by rw [← map_mul, h1, map_one]
  have hnr : ∀ r : ℚ, ‖(r : ℂ_[l])‖ = ‖(r : ℚ_[l])‖ := by
    intro r
    rw [← PadicComplex.norm_extends', map_ratCast, PadicComplex.coe_eq, map_ratCast]
  have hsum : y + y' = ((2 * p : ℚ) : ℂ_[l]) := by
    rw [← map_add]
    have : (p : ℂ) + (q : ℂ) * s + ((p : ℂ) - (q : ℂ) * s) = ((2 * p : ℚ) : ℂ) := by push_cast; ring
    rw [this, map_ratCast]
  have htr : ‖y + y'‖ ≤ 1 := by rw [hsum, hnr]; exact hT'
  have hle : ‖y‖ ≤ 1 := norm_le_one_of_trace hyy htr
  have hle' : ‖y'‖ ≤ 1 := norm_le_one_of_trace (by rw [mul_comm]; exact hyy) (by rw [add_comm]; exact htr)
  have hn : ‖y‖ * ‖y'‖ = 1 := by rw [← norm_mul, hyy, norm_one]
  nlinarith [norm_nonneg y, norm_nonneg y']

end GlobalTheory.TraceNormCoordinates
