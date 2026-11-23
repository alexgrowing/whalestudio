import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.DualEmb

open PI.UpqRep GlobalTheory.DerivedAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem hasDerivAt_inv_exp_entry (X : Mx k r) (j c : Fin (2 * r + k + 1)) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X))⁻¹ j c) (-X j c) 0 := by
  have h := Formalism.REAL.hasDerivAt_mul_exp_smul_zero 1 (-X)
  simp only [Matrix.one_mul] at h
  have h2 : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • (-X)) j c) ((-X) j c) 0 :=
    hasDerivAt_pi.1 (hasDerivAt_pi.1 h j) c
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X))⁻¹ j c) =
      fun t : ℝ => NormedSpace.exp ((t : ℂ) • (-X)) j c := by
    funext t
    rw [smul_neg, Matrix.exp_neg]
  rw [e]
  exact h2

theorem lie_part₁ (Y : Mx k r) :
    InLieHpk k r ((1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
  have hh : (Formalism.QuantumDeterminants.Hpk k r)ᴴ = Formalism.QuantumDeterminants.Hpk k r := Formalism.QuantumDeterminants.GBasic.Hpk_herm k r
  have hs : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  show (_ : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * _ = 0
  generalize Formalism.QuantumDeterminants.Hpk k r = H at hh hs
  have hs' : ∀ A : Mx k r, H * (H * A) = A := fun A => by rw [← Matrix.mul_assoc, hs, Matrix.one_mul]
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_neg, conjTranspose_mul,
    conjTranspose_conjTranspose, hh, h2, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, hs, hs', Matrix.mul_one]
  module

theorem lie_part₂ (Y : Mx k r) :
    InLieHpk k r ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
  have hh : (Formalism.QuantumDeterminants.Hpk k r)ᴴ = Formalism.QuantumDeterminants.Hpk k r := Formalism.QuantumDeterminants.GBasic.Hpk_herm k r
  have hs : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  show (_ : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * _ = 0
  generalize Formalism.QuantumDeterminants.Hpk k r = H at hh hs
  have hs' : ∀ A : Mx k r, H * (H * A) = A := fun A => by rw [← Matrix.mul_assoc, hs, Matrix.one_mul]
  have h2 : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by simp
  simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_neg, conjTranspose_mul,
    conjTranspose_conjTranspose, hh, h2, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, hs, hs', Matrix.mul_one]
  module

theorem io_dsig (hK : PI.KFinSmooth) {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}
    (hR : R.IsDS ε mu) {RI : Fin (2 * r + k + 1) → Rep k r}
    {muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ}
    {io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H} {pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H}
    (hI : ∀ s, (RI s).IsDS ε (muI s)) (hT : TensRaw dualM R RI io pr) (s : Fin (2 * r + k + 1))
    {X : Mx k r} (hX : InLieHpk k r X) {y : (RI s).H} (hy : y ∈ (RI s).sm) (c : Fin (2 * r + k + 1)) :
    io s c (dsig (k := k) (r := r) (RI s).σ X y) =
      dsig (k := k) (r := r) R.σ X (io s c y) - ∑ j, X j c • io s j y := by
  have hL := (GlobalTheory.cwCont_continuousOn_hasDerivAt hK k r ε (muI s) (RI s) (hI s) R.H (io s c) (hT.io_sm s c).add
    (hT.io_sm s c).smul ((hT.io_sm s c).cont [] (by simp)) y hy).2 X hX
  have h1 : R.σ 1 = 1 := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hR.2).1
  have e : (fun t : ℝ => io s c ((RI s).σ (NormedSpace.exp ((t : ℂ) • X)) y)) =
      fun t : ℝ => ∑ j, (NormedSpace.exp ((t : ℂ) • X))⁻¹ j c •
        R.σ (NormedSpace.exp ((t : ℂ) • X)) (io s j y) := by
    funext t
    exact congrFun (hT.io_eq s _ (exp_mem hX t) y hy) c
  rw [e] at hL
  have hR' := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (hasDerivAt_inv_exp_entry X j c).fun_smul (hasDerivAt_dsig hX ((hT.io_sm s j).mem y hy))
  rw [hL.unique hR']
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, inv_one, h1, one_apply_eq_self,
    Finset.sum_add_distrib, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

end GlobalTheory.DualEmb

namespace GlobalTheory

open DualEmb

theorem dualTens_io_dC : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (RI : Fin (2 * r + k + 1) → Rep k r) (muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H), (∀ s, (RI s).IsDS ε (muI s)) → TensRaw dualM R RI io pr → ∀ s Y, ∀ y ∈ (RI s).sm, ∀ c, io s c ((RI s).dC Y y) = R.dC Y (io s c y) - ∑ j, Y j c • io s j y := by
  intro hK k r ε mu R hR RI muI io pr hI hT s Y y hy c
  have h1 := lie_part₁ Y
  have h2 := lie_part₂ Y
  have hY : Y = (1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)) +
      Complex.I • ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
    have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
      field_simp
    rw [smul_smul, hI]
    module
  unfold Rep.dC
  generalize (1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)) = X₁ at h1 hY ⊢
  generalize (1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)) = X₂ at h2 hY ⊢
  have m1 := DerivedAction.dsig_smooth (hI s).2 h1 hy
  have m2 := DerivedAction.dsig_smooth (hI s).2 h2 hy
  rw [(hT.io_sm s c).add _ m1 _ ((RI s).smSub.smul_mem _ m2), (hT.io_sm s c).smul _ _ m2,
    io_dsig hK hR hI hT s h1 hy c, io_dsig hK hR hI hT s h2 hy c, hY]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_smul, mul_smul, Finset.sum_add_distrib,
    ← Finset.smul_sum, smul_sub]
  abel

end GlobalTheory

end
