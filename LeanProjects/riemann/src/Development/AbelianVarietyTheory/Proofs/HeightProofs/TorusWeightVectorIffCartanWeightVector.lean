import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.RealPar.TorusWt

variable {p q n : ℕ}

def torX (θ : Ix p q → ℝ) : Mat p q := Matrix.diagonal fun a => (θ a : ℂ) * Complex.I

theorem torX_mem (θ : Ix p q → ℝ) : torX θ ∈ upq p q := by
  change _ = _
  ext a b
  have hJ : TH.Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [TH.Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp
  rw [hJ, torX, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_add]
  by_cases h : a = b
  · subst h; simp; ring
  · simp [h]

theorem smul_torX (t : ℝ) (θ : Ix p q → ℝ) : t • torX θ = torX fun a => t * θ a := by
  ext a b
  by_cases h : a = b
  · subst h; simp [torX, mul_assoc]
  · simp [torX, h]

theorem torX_eq_sum (θ : Ix p q → ℝ) : torX θ = ∑ a, ((θ a : ℂ) * Complex.I) • Eab a a := by
  ext a b
  simp only [torX, Eab, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro c _ hc; simp [hc]
  · simp

theorem reindex_cov_expt (T : GrpData p q) (e : Ix p q ≃ Fin n) (θ : Fin n → ℝ) :
    Matrix.reindex e e ((T.cov (T.expt (torX fun a => θ (e a))) : GL (Ix p q) ℂ) : Mat p q) =
      Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I) := by
  rw [T.expt_cov _ (torX_mem _), torX, Matrix.exp_diagonal]
  ext i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  simp [Matrix.diagonal_apply, Pi.coe_exp, Complex.exp_eq_exp_ℂ]

theorem diag_mem_Kset (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp [← Complex.exp_conj, ← Complex.exp_add]
  · rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

theorem flow_eq {T : GrpData p q} (R : DSRep T) {X : Mat p q} (hX : X ∈ upq p q) {v : R.HK.V} {c : ℂ}
    (hv : R.HK.act X v = c • v) : R.U.π (T.expt X) (R.ι v) = Complex.exp c • R.ι v := by
  set f : ℝ → R.U.H := fun t => R.U.π (T.expt (t • X)) (R.ι v) with hf
  have hd : ∀ t, HasDerivAt f (c • f t) t := by
    intro t
    have h0 := R.der X hX v
    rw [hv, map_smul] at h0
    have h1 : HasDerivAt (fun s : ℝ => f (s - t)) (c • R.ι v) t := by
      have := HasDerivAt.comp_sub_const t t (f := f) (f' := c • R.ι v) (by rw [sub_self]; exact h0)
      exact this
    have h2 := ((R.U.π (T.expt (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
    convert h2 using 1
    · funext s
      simp only [hf, Function.comp, ContinuousLinearMap.coe_restrictScalars']
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← T.expt_add X hX, add_sub_cancel]
    · simp [hf]
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(c * t)) • f t) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(c * t))) (Complex.exp (-(c * t)) * (-c)) t := by
      have : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).fun_neg
      exact this.cexp
    convert h1.fun_smul (hd t) using 1
    rw [smul_smul, ← add_smul]; simp
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [hf, one_smul, zero_smul, T.expt_zero, map_one, Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero,
    neg_zero, Complex.exp_zero, ContinuousLinearMap.one_apply] at hc
  conv_rhs => rw [← hc, smul_smul, ← Complex.exp_add]
  simp

theorem isWtOn_iff : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ (μ : Fin n → ℝ) (v : R.HK.V), IsWtOn (Formalism.REAL.Kset ε) σ μ (R.ι v) ↔ ∀ a, R.HK.act (Eab a a) v = ((μ (e a) : ℝ) : ℂ) • v := by
  intro p q n e ε T R σ _ hF μ v
  have key : ∀ θ : Fin n → ℝ, R.U.π (T.expt (torX fun a => θ (e a))) =
      σ (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) := fun θ => by
    rw [hF, reindex_cov_expt]
  constructor
  · intro h a
    set θ : Fin n → ℝ := Pi.single (e a) 1 with hθ
    have h0 := R.der _ (torX_mem fun b => θ (e b)) v
    have h1 : (fun t : ℝ => R.U.π (T.expt (t • torX fun b => θ (e b))) (R.ι v)) =
        fun t : ℝ => Complex.exp ((μ (e a) * Complex.I) * t) • R.ι v := by
      funext t
      rw [smul_torX, key fun b => t * θ b, h _ (diag_mem_Kset ε _)]
      congr 2
      rw [Finset.sum_eq_single (e a)]
      · simp [hθ]; ring
      · intro c _ hc; simp [hθ, hc]
      · simp
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp ((μ (e a) * Complex.I) * t) • R.ι v)
        ((μ (e a) * Complex.I) • R.ι v) 0 := by
      have : HasDerivAt (fun t : ℝ => ((μ (e a) * Complex.I) * (t : ℂ))) (μ (e a) * Complex.I) 0 := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).const_mul (μ (e a) * Complex.I))
      simpa using this.cexp.smul_const (R.ι v)
    rw [h1] at h0
    have h3 := h0.unique h2
    rw [← map_smul] at h3
    have h4 := R.ι_inj h3
    have h5 : (torX fun b => θ (e b)) = Complex.I • Eab a a := by
      rw [torX_eq_sum, Finset.sum_eq_single a]
      · simp [hθ]
      · intro c _ hc; simp [hθ, hc]
      · simp
    rw [h5, map_smul, LinearMap.smul_apply, mul_comm, mul_smul] at h4
    exact smul_right_injective _ Complex.I_ne_zero h4
  · intro h θ _
    rw [← key]
    apply flow_eq R (torX_mem _)
    rw [torX_eq_sum, map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, h, smul_smul, ← Finset.sum_smul]
    congr 1
    rw [← e.sum_comp]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring

end GlobalTheory.RealPar.TorusWt

end
