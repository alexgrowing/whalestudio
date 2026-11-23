import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraOfIsCutOutByRealMatrixAlgebra
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwConstMin

variable {n : ℕ}

private lemma hs_eq_re_trace' (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs X = ((X * Xᴴ).trace).re := by
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem hs_unitary_sub_one {u : Matrix (Fin n) (Fin n) ℂ} (hu : uᴴ * u = 1) :
    Formalism.REAL.hs (u - 1) = 2 * ((1 : Matrix (Fin n) (Fin n) ℂ).trace).re - 2 * (u.trace).re := by
  have h2 : u * uᴴ = 1 := mul_eq_one_comm.mp hu
  rw [hs_eq_re_trace', conjTranspose_sub, conjTranspose_one]
  have e : (u - 1) * (uᴴ - 1) = 1 - u - uᴴ + 1 := by
    rw [sub_mul, mul_sub, mul_sub, h2, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [e, trace_add, trace_sub, trace_sub, trace_conjTranspose]
  simp only [Complex.add_re, Complex.sub_re, Complex.star_def, Complex.conj_re]
  ring

theorem re_trace_eq_zero_of_max (X u : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, ((NormedSpace.exp ((t : ℂ) • X) * u).trace).re ≤ (u.trace).re) : ((X * u).trace).re = 0 := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  let φ : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (Complex.reLm ∘ₗ Matrix.traceLinearMap (Fin n) ℝ ℂ)
  have hφ : ∀ M, φ M = (M.trace).re := fun M => rfl
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) * u)
      (NormedSpace.exp ((0 : ℝ) • X) * X * u) 0 :=
    (hasDerivAt_exp_smul_const X (0 : ℝ)).mul_const u
  have hf : HasDerivAt (fun t : ℝ => φ (NormedSpace.exp (t • X) * u))
      (φ (NormedSpace.exp ((0 : ℝ) • X) * X * u)) 0 :=
    φ.hasFDerivAt.comp_hasDerivAt 0 hd
  have hmax : IsLocalMax (fun t : ℝ => φ (NormedSpace.exp (t • X) * u)) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [hφ, zero_smul, NormedSpace.exp_zero, Matrix.one_mul]
    have := h t
    rwa [GlobalTheory.IwTangent.coe_smul_eq] at this
  have h0 := hmax.hasDerivAt_eq_zero hf
  simpa [hφ, NormedSpace.exp_zero] using h0

theorem uMat_mul' {ε : Fin n → Bool} (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem maxK_mul {ε : Fin n → Bool} {g h : Formalism.REAL.UJ ε} (hg : g ∈ maxK ε) (hh : h ∈ maxK ε) : g * h ∈ maxK ε := by
  have hg' : (uMat g)ᴴ * uMat g = 1 := hg
  have hh' : (uMat h)ᴴ * uMat h = 1 := hh
  show (uMat (g * h))ᴴ * uMat (g * h) = 1
  rw [uMat_mul', conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (uMat g)ᴴ, hg',
    Matrix.one_mul, hh']

theorem exists_nearest : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → S ⊆ maxK ε → (∀ i, (E i)ᴴ = -E i) → ∀ k ∈ maxK ε, ∃ l ∈ S, crd E (uMat (l * k) - 1) = 0 ∧ ∀ l' ∈ S, nrm (uMat (l * k) - 1) ≤ nrm (uMat (l' * k) - 1) := by
  intro n ε S d E hcut hSK hE k hk
  obtain ⟨H, hHS, hSc⟩ := IsCut.subgroup hcut
  have hmemS : ∀ g, g ∈ S ↔ g ∈ H := fun g => by rw [← hHS]; rfl
  have hcpt : IsCompact S := (isCompact_maxK ε).of_isClosed_subset hSc hSK
  have hne : S.Nonempty := ⟨1, (hmemS 1).2 H.one_mem⟩
  have hcont : Continuous fun l : Formalism.REAL.UJ ε => nrm (uMat (l * k) - 1) :=
    (continuous_nrm_uMat ε).comp (continuous_mul_const k)
  obtain ⟨l, hlS, hmin⟩ := hcpt.exists_isMinOn hne hcont.continuousOn
  refine ⟨l, hlS, ?_, fun l' hl' => hmin hl'⟩
  set w := uMat (l * k) with hw
  have hwK : l * k ∈ maxK ε := maxK_mul (hSK hlS) hk
  have hwU : wᴴ * w = 1 := hwK
  funext i
  have hflow := (GlobalTheory.IwTangent.lie_algebra_of_isCut n ε S d E hcut).1 (E i)
    (Submodule.subset_span ⟨i, rfl⟩)
  have hle : ∀ t : ℝ, ((NormedSpace.exp ((t : ℂ) • E i) * w).trace).re ≤ (w.trace).re := by
    intro t
    obtain ⟨g, hgS, hg⟩ := hflow t
    have hgl : g * l ∈ S := (hmemS _).2 (H.mul_mem ((hmemS _).1 hgS) ((hmemS _).1 hlS))
    have hv : uMat (g * l * k) = NormedSpace.exp ((t : ℂ) • E i) * w := by
      rw [mul_assoc, uMat_mul', hg]
    have hvK : (uMat (g * l * k))ᴴ * uMat (g * l * k) = 1 := maxK_mul (hSK hgl) hk
    have hn : nrm (w - 1) ≤ nrm (uMat (g * l * k) - 1) := hmin hgl
    have hsq : Formalism.REAL.hs (w - 1) ≤ Formalism.REAL.hs (uMat (g * l * k) - 1) := by
      rw [← nrm_sq, ← nrm_sq]
      exact pow_le_pow_left₀ (nrm_nonneg _) hn 2
    rw [hs_unitary_sub_one hwU, hs_unitary_sub_one hvK, hv] at hsq
    linarith
  have hz : ((E i * w).trace).re = 0 := re_trace_eq_zero_of_max (E i) w hle
  have htr : ((E i).trace).re = 0 := by
    have h1 := congrArg (fun M => (M.trace).re) (hE i)
    simp only [trace_conjTranspose, Complex.star_def, Complex.conj_re, trace_neg, Complex.neg_re] at h1
    linarith
  have hcomm : ((w * E i).trace).re = ((E i * w).trace).re := by rw [trace_mul_comm]
  show ((( w - 1) * (E i)ᴴ).trace).re = 0
  rw [hE i, sub_mul, Matrix.mul_neg, Matrix.mul_neg, Matrix.one_mul, trace_sub, trace_neg, trace_neg,
    Complex.sub_re, Complex.neg_re, Complex.neg_re, hcomm, hz, htr]
  simp

end GlobalTheory.IwConstMin
