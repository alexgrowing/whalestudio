import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaTransl

variable {p : ℕ} [Fact p.Prime]

theorem norm_lamC_root_mul (lam : Qbar →+* ℂ_[p]) {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1)
    (x : ℂ) : ‖lamC lam (ζ * x)‖ = ‖lamC lam x‖ := by
  have hq : ζ ∈ Qbar := by
    refine mem_algebraicClosure_iff.2 ⟨Polynomial.X ^ n - Polynomial.C 1,
      Polynomial.X_pow_sub_C_ne_zero hn 1, ?_⟩
    simp [hζ]
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hζ
    exact zero_ne_one hζ
  have h1 : ‖lam ⟨ζ, hq⟩‖ = 1 := by
    have e : (⟨ζ, hq⟩ : Qbar) ^ n = 1 := Subtype.ext (by simpa using hζ)
    have : ‖lam ⟨ζ, hq⟩‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, e, map_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  by_cases hx : x ∈ Qbar
  · have hzx : ζ * x ∈ Qbar := mul_mem hq hx
    simp only [lamC, dif_pos hx, dif_pos hzx]
    have : (⟨ζ * x, hzx⟩ : Qbar) = ⟨ζ, hq⟩ * ⟨x, hx⟩ := rfl
    rw [this, map_mul, norm_mul, h1, one_mul]
  · have hzx : ζ * x ∉ Qbar := by
      intro h
      apply hx
      have : x = ζ⁻¹ * (ζ * x) := by field_simp
      rw [this]
      exact mul_mem (inv_mem hq) h
    simp only [lamC, dif_neg hx, dif_neg hzx]

theorem cval_norm_periodic : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → ∀ t ω : ℂ, InRationalLattice g.abelian₂ t → ω ∈ g.abelian₂ → ‖GlobalTheory.ThetaTransl.cval g (t + ω)‖ = ‖GlobalTheory.ThetaTransl.cval g t‖ := by
  intro D p _ cc δ g hg t ω ht hω
  obtain ⟨hcc, -, hδ, hΛ, -⟩ := hg
  have hlat := (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ ⟨hcc, hδ⟩).1
  rw [← hΛ] at hlat
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair g.abelian₂ hlat
  have hlaw := (GlobalTheory.OddTheta.sgStar_laws g.abelian₂ hlat).1.2.2.2 ω hω t
  obtain ⟨m, hm, hmt⟩ := ht
  set s := sgStar g.abelian₂ with hs
  set A : ℂ := (area g.abelian₂ : ℂ) with hAdef
  have hA : area g.abelian₂ = GlobalTheory.latticeArea L := GlobalTheory.OddTheta.area_eq L g.abelian₂ hL
  have hA0 : A ≠ 0 := by
    rw [hAdef, hA]; exact_mod_cast (GlobalTheory.latticeArea_pos L).ne'
  set ψ : ℂ := if ω / 2 ∈ g.abelian₂ then 1 else -1 with hψ
  set E : ℂ := Complex.exp ((Real.pi : ℂ) * (t * (starRingEnd ℂ) ω - ω * (starRingEnd ℂ) t) / (2 * A)) with hE
  have key : U1 g.abelian₂ (t + ω) s 0 = (ψ * E) * U1 g.abelian₂ t s 0 := by
    have h2 : s (t + ω) = ψ * s t * Complex.exp (-(-(Real.pi : ℂ) * t * (starRingEnd ℂ) ω / A -
        (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * A))) := by
      have hlaw' := hlaw
      simp only [U1] at hlaw'
      rw [← hlaw', mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    simp only [U1]
    rw [zero_add, zero_add, h2, show ψ * E * (s t * Complex.exp (-(Real.pi : ℂ) * 0 * (starRingEnd ℂ) t / A -
        (Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * A))) = ψ * s t * (E * Complex.exp (-(Real.pi : ℂ) * 0 *
        (starRingEnd ℂ) t / A - (Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * A))) by ring,
      hE, ← Complex.exp_add, mul_assoc (ψ * s t), ← Complex.exp_add]
    congr 1
    congr 1
    simp only [map_add]
    ring
  have hroot : (ψ * E) ^ (2 * m) = 1 := by
    have hψ2 : ψ ^ 2 = 1 := by rw [hψ]; split_ifs <;> norm_num
    have ha' : (m : ℂ) * t ∈ L.lattice := (hL _).1 hmt
    have hω' : ω ∈ L.lattice := (hL _).1 hω
    obtain ⟨k, hk⟩ := GlobalTheory.exists_int_im_latticeForm L ha' hω'
    have hL0 : (GlobalTheory.latticeArea L : ℂ) ≠ 0 := by exact_mod_cast (GlobalTheory.latticeArea_pos L).ne'
    have him : ((m : ℂ) * t * (starRingEnd ℂ) ω).im = k * GlobalTheory.latticeArea L := by
      rw [GlobalTheory.latticeForm, Complex.div_ofReal_im, div_eq_iff (GlobalTheory.latticeArea_pos L).ne'] at hk
      exact hk
    have hc : (starRingEnd ℂ) ((m : ℂ) * t * (starRingEnd ℂ) ω) = (m : ℂ) * (starRingEnd ℂ) t * ω := by
      simp [map_mul]
    have hsub := Complex.sub_conj ((m : ℂ) * t * (starRingEnd ℂ) ω)
    rw [hc, him] at hsub
    have hexp : ((2 * m : ℕ) : ℂ) * ((Real.pi : ℂ) * (t * (starRingEnd ℂ) ω - ω * (starRingEnd ℂ) t) / (2 * A)) =
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      calc ((2 * m : ℕ) : ℂ) * ((Real.pi : ℂ) * (t * (starRingEnd ℂ) ω - ω * (starRingEnd ℂ) t) / (2 * A))
          = (Real.pi : ℂ) * ((m : ℂ) * t * (starRingEnd ℂ) ω - (m : ℂ) * (starRingEnd ℂ) t * ω) / A := by
            push_cast; field_simp
        _ = (Real.pi : ℂ) * (((2 * (k * GlobalTheory.latticeArea L) : ℝ) : ℂ) * Complex.I) / A := by rw [hsub]
        _ = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
            rw [hAdef, hA]; push_cast; field_simp
    rw [mul_pow, pow_mul, hψ2, one_pow, one_mul, hE, ← Complex.exp_nat_mul, hexp,
      Complex.exp_int_mul_two_pi_mul_I]
  unfold cval
  rw [key]
  exact norm_lamC_root_mul g.lam (by omega) hroot _

end GlobalTheory.ThetaTransl
