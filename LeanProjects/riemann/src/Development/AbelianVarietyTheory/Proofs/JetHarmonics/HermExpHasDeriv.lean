import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

noncomputable section

namespace GlobalTheory.TensorDualDifferential

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def hermLin {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ where
  toFun M := herm H (M *ᵥ v) w
  map_add' M N := by simp [herm, Matrix.add_mulVec, Matrix.mulVec_add]
  map_smul' c M := by simp [herm, Matrix.smul_mulVec, Matrix.mulVec_smul]

theorem herm_exp_hasDeriv {n : ℕ} (H X : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    HasDerivAt (fun t : ℝ => herm H (NormedSpace.exp ((t : ℂ) • X) *ᵥ v) w) (herm H (X *ᵥ v) w) 0 := by
  have h : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 :=
    hasDerivAt_iff_tendsto_slope.2 (Formalism.REAL.tendsto_slope_exp_smul X)
  exact (((LinearMap.toContinuousLinearMap (hermLin H v w)).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt
    (0 : ℝ) h

theorem herm_skew {n : ℕ} {H X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * H + H * X = 0) (v w : Fin n → ℂ) :
    herm H v (X *ᵥ w) = -herm H (X *ᵥ v) w := by
  have h : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h,
    Matrix.neg_mulVec, dotProduct_neg]

theorem dOp_tensor {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (V →L[ℂ] V)} {B : Fin k → (Fin (2 * r + k + 1) → ℂ)}
    {πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V)))}
    (hπ : IsRepW k r z π) (hπt : IsRepW k r z πt) (hB : IsFrameOf k r [z] B)
    (h : ∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, star (herm (Hpk k r) (h *ᵥ B d) (B c)) • π h (y d))
    {X : Mx k r} (hX : InLieW k r z X) (y : PiLp 2 (fun _ : Fin k => V)) (c : Fin k) :
    dOp πt X y c = dOp π X (y c) - ∑ d, hermLin (Hpk k r) (B c) (B d) X • y d := by
  have h1 := dOp_hasDeriv hπt.1 hπt.2 hX
  have h2 := dOp_hasDeriv hπ.1 hπ.2 hX
  have h3 : HasDerivAt (fun t : ℝ => πt (NormedSpace.exp ((t : ℂ) • X)) y c) (dOp πt X y c) 0 :=
    (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin k => V) c).comp
      (ContinuousLinearMap.apply ℂ _ y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h4 : ∀ d, HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) (y d)) (dOp π X (y d)) 0 :=
    fun d => ((ContinuousLinearMap.apply ℂ V (y d)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h5 := HasDerivAt.fun_sum (u := Finset.univ) fun d _ =>
    (herm_exp_hasDeriv (Hpk k r) X (B d) (B c)).star.fun_smul (h4 d)
  have h6 : (fun t : ℝ => πt (NormedSpace.exp ((t : ℂ) • X)) y c) = fun t : ℝ =>
      ∑ d, star (herm (Hpk k r) (NormedSpace.exp ((t : ℂ) • X) *ᵥ B d) (B c)) •
        π (NormedSpace.exp ((t : ℂ) • X)) (y d) := funext fun t => h _ (exp_uw hX t) y c
  rw [h6] at h3
  rw [h3.unique h5, Finset.sum_add_distrib]
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec, hπ.1.1, hB.2.1,
    Qx2.herm_star, herm_skew hX.1.1]
  simp [hermLin, sub_eq_add_neg]

theorem EB_tensor : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V)))), inWb k r z → 0 < Tz k r z → IsRepW k r z π → IsRepW k r z πt → IsFrameOf k r [z] B → (∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, star (herm (Hpk k r) (h *ᵥ B d) (B c)) • π h (y d)) → ∀ a b y c, EB πt B a b y c = EB π B a b (y c) - if c = b then y a else 0 := by
  intro V _ _ _ k r z π B πt _ _ hπ hπt hB h a b y c
  have hl := frame_lie hB a b
  have e1 := dOp_tensor hπ hπt hB h hl.1 y c
  have e2 := dOp_tensor hπ hπt hB h hl.2 y c
  have e3 : ∑ d, hermLin (Hpk k r) (B c) (B d) (hpart1 (Hpk k r) (unitB (Hpk k r) B a b)) • y d +
      Complex.I • ∑ d, hermLin (Hpk k r) (B c) (B d) (hpart2 (Hpk k r) (unitB (Hpk k r) B a b)) • y d =
      if c = b then y a else 0 := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    have e4 : ∀ d, hermLin (Hpk k r) (B c) (B d) (hpart1 (Hpk k r) (unitB (Hpk k r) B a b)) • y d +
        Complex.I • hermLin (Hpk k r) (B c) (B d) (hpart2 (Hpk k r) (unitB (Hpk k r) B a b)) • y d =
        if a = d then (if c = b then y d else 0) else 0 := by
      intro d
      rw [smul_smul, ← add_smul, ← smul_eq_mul Complex.I, ← map_smul, ← map_add, LieListProducts.hsum]
      have e5 : hermLin (Hpk k r) (B c) (B d) (unitB (Hpk k r) B a b) =
          herm (Hpk k r) (B c) (B b) * herm (Hpk k r) (B a) (B d) := by
        show herm (Hpk k r) (unitB (Hpk k r) B a b *ᵥ B c) (B d) = _
        rw [Qx8.unitB_mulVec]
        simp [herm, Matrix.mulVec_smul]
      rw [e5, hB.2.1, hB.2.1]
      split_ifs <;> simp
    simp [e4]
  have e6 : EB πt B a b y c = dOp πt (hpart1 (Hpk k r) (unitB (Hpk k r) B a b)) y c +
      Complex.I • dOp πt (hpart2 (Hpk k r) (unitB (Hpk k r) B a b)) y c := rfl
  have e7 : EB π B a b (y c) = dOp π (hpart1 (Hpk k r) (unitB (Hpk k r) B a b)) (y c) +
      Complex.I • dOp π (hpart2 (Hpk k r) (unitB (Hpk k r) B a b)) (y c) := rfl
  rw [e6, e7, e1, e2, ← e3, smul_sub]
  abel

end GlobalTheory.TensorDualDifferential
