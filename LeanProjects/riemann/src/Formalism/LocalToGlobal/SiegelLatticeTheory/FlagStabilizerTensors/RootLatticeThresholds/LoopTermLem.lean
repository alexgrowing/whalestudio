import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic

noncomputable section

open scoped Classical
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf.LTL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def pt0 (D : D7) : Point ℂ (D.R.rS + 1) := ⟨[(1, D.R.rS + 1)], by simp, by simp⟩

section Lemmas

open scoped ComplexConjugate

theorem hsNormSq_nonneg {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  first
  | exact inner_self_nonneg (𝕜 := ℂ) (x := A (stdOrthonormalBasis ℂ Wq i))
  | (rw [inner_self_eq_norm_sq_to_K]; norm_cast; positivity)

theorem hsNormSq_smul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (c : ℂ) (A : Wq →L[ℂ] Wp) :
    hsNormSq (c • A) = Complex.normSq c * hsNormSq A := by
  unfold hsNormSq hsInner
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right, ← mul_assoc]
  rw [← Finset.mul_sum]
  first
  | rw [Complex.mul_conj]
  | rw [← Complex.normSq_eq_conj_mul_self]
  rw [Complex.re_ofReal_mul]

theorem isQuotMeas_smul {k r : ℕ} {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)} (h : IsQuotMeas μG μS ν) {c : ENNReal}
    (h0 : c ≠ 0) (hT : c ≠ ⊤) : IsQuotMeas μG (c • μS) (c⁻¹ • ν) := by
  intro f hf
  rw [h f hf]
  simp only [MeasureTheory.lintegral_smul_measure, smul_eq_mul]
  rw [MeasureTheory.lintegral_const_mul' c _ hT, ← mul_assoc, ENNReal.inv_mul_cancel h0 hT, one_mul]

theorem locJ_smul {k r : ℕ} {W : LocW k r} (A : LocS W) (ν : Measure (Formalism.QuantumDeterminants.Mt k r)) (c : ENNReal)
    (γ : MatKR k r) : A.J (c • ν) γ = ((c.toReal : ℝ) : ℂ) • A.J ν γ := by
  simp only [Formalism.MainNotions.S.LocS.J, Formalism.MainNotions.S.ampJ, MeasureTheory.integral_smul_measure]
  rw [Complex.coe_smul]
  exact smul_comm _ _ _

end Lemmas

section Tr

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem star_dot_conjT {n m : Type*} [Fintype n] [Fintype m] (Q : Matrix n m ℂ) (x : m → ℂ) (y : n → ℂ) :
    star x ⬝ᵥ (Qᴴ *ᵥ y) = star (Q *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem hJ_smul_real {n : ℕ} (ε : Fin n → Bool) (r s : ℝ) (x y : Fin n → ℂ) :
    hJ ε ((r : ℂ) • x) ((s : ℂ) • y) = ((r * s : ℝ) : ℂ) * hJ ε x y := by
  simp only [hJ]
  simp [Matrix.mulVec_smul, smul_eq_mul]
  try push_cast
  try ring

theorem frS_pow (D : D7) (a : Fin (D.R.rS + 1)) (h : a.val < D.R.rS) :
    frS D ^ (D.R.rS - a.val) = ((rhoF D a : ℝ) : ℂ) := by
  have hk : D.host.ka / (2 * Real.pi) = D.host.rdE⁻¹ := by
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    have hpi := Real.pi_pos.ne'
    rcases eq_or_ne D.host.rdE 0 with h0 | h0
    · rw [h0]
      simp
    · field_simp
      try ring
  have hnn : 0 ≤ D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_nonneg (abs_nonneg _) _
  have hc : ((D.R.rS - a.val : ℕ) : ℝ) = (D.R.rS : ℝ) - (a.val : ℝ) := by
    rw [Nat.cast_sub h.le]
  unfold frS rhoF
  rw [hk, ← hc, Real.rpow_neg hnn, Real.rpow_natCast, ← inv_pow]
  push_cast
  try ring

theorem rhoF_last (D : D7) : rhoF D (Fin.last D.R.rS) = 1 := by
  simp [rhoF, Fin.val_last]

theorem Q_fvec (u : D.what₂.Word) (τ : D.what₂.Tau) (a : Fin (D.R.rS + 1)) :
    C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) a =
      ((rhoF D a : ℝ) : ℂ) • rv X.B.I (vOf X τ) (X.crd ((X.Fu u).fvec a)) := by
  obtain ⟨_, hQQi, _, hEv⟩ := C.isT τ
  by_cases h : a.val < D.R.rS
  · have h1 := (hEv ⟨a.val, h⟩ ⟨a.val, h⟩ rfl).1
    have ha : a = Fin.castSucc ⟨a.val, h⟩ := Fin.ext rfl
    have h2 : (X.Fu u).fvec (Fin.castSucc ⟨a.val, h⟩) = X.eX ⟨a.val, h⟩ := by
      simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
      exact congrFun (X.Fu_e u) _
    rw [← ha] at h2
    rw [h2, ← frS_pow D a h, Formalism.QuantumDeterminants.fvec, dif_pos h, Formalism.QuantumDeterminants.bvec, h1]
    rfl
  · have ha : a = Fin.last D.R.rS := Fin.ext (by have := a.isLt; simp; omega)
    subst ha
    have h3 : (X.Fu u).fvec (Fin.last D.R.rS) = X.zu u := by
      simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]
      exact X.flagZVector u
    rw [h3, rhoF_last, Formalism.QuantumDeterminants.fvec, dif_neg h]
    simp only [zB, Complex.ofReal_one, one_smul]
    rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
    rfl

theorem tau_nonempty (D : D7) : Nonempty D.what₂.Tau := by
  exact D.eTau.nonempty

theorem trG_mem {n m : ℕ} {ε : Fin n → Bool} (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ)
    (H : Matrix (Fin m) (Fin m) ℂ) (hQQi : Q * Qi = 1) (hH : Qᴴ * Formalism.REAL.Jm ε * Q = H) (g : Formalism.REAL.UJ ε) :
    Formalism.L2.SG.RealObj.trG Q Qi g ∈ Formalism.QuantumDeterminants.UH H := by
  have hU : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := by
    first
    | exact g.2
    | (unfold uMat; exact g.2)
    | simpa [uMat] using g.2
  have h1 : ∀ X : Matrix (Fin n) (Fin m) ℂ, Qiᴴ * (Qᴴ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hQQi, Matrix.conjTranspose_one, Matrix.one_mul]
  have h2 : ∀ X : Matrix (Fin n) (Fin m) ℂ, Q * (Qi * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, hQQi, Matrix.one_mul]
  have h3 : ∀ X : Matrix (Fin n) (Fin m) ℂ,
      (uMat g)ᴴ * (Formalism.REAL.Jm ε * (uMat g * X)) = Formalism.REAL.Jm ε * X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU]
  show (Qi * uMat g * Q)ᴴ * H * (Qi * uMat g * Q) = H
  rw [← hH]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, h1, h2, h3]

theorem tz_zB (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) = ((Tu D u : ℕ) : ℝ) := by
  obtain ⟨_, hQQi, hH, _⟩ := C.isT τ
  have hT' : (VS D).hT (Formalism.L2.SG.Pf.Level.toV X (X.zR u)) (Formalism.L2.SG.Pf.Level.toV X (X.zR u)) =
      -(((D.mem u).A.T : ℕ) : D.host.E) := by
    rw [show X.zR u = X.crd (X.zu u) from rfl, Formalism.L2.SG.Pf.Level.toV_crd, X.zu_norm]
  have hι := Formalism.L2.SG.Pf.Level.iota_hE (X := X) (X.zR u) (X.zR u)
  rw [hT'] at hι
  have hJv := Formalism.L2.SG.Pf.Level.hJ_rv (X := X) (vOf X τ) (X.zR u) (X.zR u)
  rw [X.φ_eq, hι] at hJv
  simp only [hJ, map_neg, map_natCast] at hJv
  unfold Formalism.QuantumDeterminants.Tz zB Formalism.QuantumDeterminants.herm
  rw [← hH, Matrix.mulVec_mulVec,
    Matrix.mul_assoc ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ))) (C.Q τ) (C.Qi τ), hQQi,
    Matrix.mul_one, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec, hJv]
  simp [Tu]

end Tr

end Formalism.L2.SG.Pf.LTL
