import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

noncomputable section

namespace GlobalTheory

theorem intertwiner_exp_of_intertwiner {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [FiniteDimensional ℂ V₁]
    {V₂ : Type} [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [FiniteDimensional ℂ V₂]
    (T : V₁ →ₗ[ℂ] V₂) {A₁ : V₁ →L[ℂ] V₁} {A₂ : V₂ →L[ℂ] V₂} (h : ∀ v, T (A₁ v) = A₂ (T v)) (v : V₁) :
    T (NormedSpace.exp A₁ v) = NormedSpace.exp A₂ (T v) := by
  have : CompleteSpace V₁ := FiniteDimensional.complete ℂ V₁
  have : CompleteSpace V₂ := FiniteDimensional.complete ℂ V₂
  have hp : ∀ n : ℕ, ∀ v, T ((A₁ ^ n) v) = (A₂ ^ n) (T v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, ih, h]
  have h1 := ((LinearMap.toContinuousLinearMap T).comp (ContinuousLinearMap.apply ℂ V₁ v)).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A₁)
  have h2 := (ContinuousLinearMap.apply ℂ V₂ (T v)).hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A₂)
  refine h1.unique (h2.congr_fun ?_)
  intro n
  show T (((n.factorial : ℂ)⁻¹) • (A₁ ^ n) v) = ((n.factorial : ℂ)⁻¹) • (A₂ ^ n) (T v)
  rw [map_smul, hp]

theorem intertwiner_dOp_of_EB {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [FiniteDimensional ℂ V₁]
    {V₂ : Type} [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [FiniteDimensional ℂ V₂] {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π₁ : Mx k r → (V₁ →L[ℂ] V₁)} {π₂ : Mx k r → (V₂ →L[ℂ] V₂)} (T : V₁ →ₗ[ℂ] V₂)
    {B : Fin k → Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hzz : herm (Hpk k r) z z ≠ 0)
    (h₁ : IsRepW k r z π₁) (h₂ : IsRepW k r z π₂) (hB : IsFrameOf k r [z] B)
    (hT : ∀ a b v, T (EB π₁ B a b v) = EB π₂ B a b (T v)) {X : Mx k r} (hX : InLieW k r z X) :
    ∀ v, T (dOp π₁ X v) = dOp π₂ X (T v) := by
  have hE := elementary_lie_elements
  let Gd : Mx k r → Prop := fun Z => InGlW k r z Z ∧ ∀ v, T (ecOp π₁ Z v) = ecOp π₂ Z (T v)
  have gadd : ∀ Z Z', Gd Z → Gd Z' → Gd (Z + Z') := by
    intro Z Z' h h'
    have e₁ := (hE V₁ k r z π₁ h₁ Z Z' h.1 h'.1).1
    have e₂ := (hE V₂ k r z π₂ h₂ Z Z' h.1 h'.1).1
    refine ⟨e₁.1, fun v => ?_⟩
    rw [e₁.2, e₂.2, _root_.add_apply, _root_.add_apply, map_add, h.2, h'.2]
  have gsmul : ∀ (c : ℂ) Z, Gd Z → Gd (c • Z) := by
    intro c Z h
    have e₁ := (hE V₁ k r z π₁ h₁ Z Z h.1 h.1).2.1 c
    have e₂ := (hE V₂ k r z π₂ h₂ Z Z h.1 h.1).2.1 c
    refine ⟨e₁.1, fun v => ?_⟩
    rw [e₁.2, e₂.2, _root_.smul_apply, _root_.smul_apply, map_smul, h.2]
  have g0 : Gd 0 := by
    refine ⟨SkewHermitianParts.inGl_zero z, fun v => ?_⟩
    have e₁ := ((hE V₁ k r z π₁ h₁ 0 0 (SkewHermitianParts.inGl_zero z) (SkewHermitianParts.inGl_zero z)).2.1 0).2
    have e₂ := ((hE V₂ k r z π₂ h₂ 0 0 (SkewHermitianParts.inGl_zero z) (SkewHermitianParts.inGl_zero z)).2.1 0).2
    rw [zero_smul, zero_smul] at e₁ e₂
    rw [e₁, e₂]
    simp
  have gu : ∀ a b, Gd (unitB (Hpk k r) B a b) := fun a b => ⟨frame_lie hB a b, fun v => hT a b v⟩
  have hsum : Gd (∑ a, ∑ b, herm (Hpk k r) (X *ᵥ B b) (B a) • unitB (Hpk k r) B a b) :=
    Finset.sum_induction _ Gd gadd g0 fun a _ =>
      Finset.sum_induction _ Gd gadd g0 fun b _ => gsmul _ _ (gu a b)
  rw [← SkewHermitianParts.lie_expand hz hzz hB hX] at hsum
  have e₁ : ecOp π₁ X = dOp π₁ X := by
    unfold ecOp
    rw [SkewHermitianParts.hpart1_skew hX.1.1, SkewHermitianParts.hpart2_skew hX.1.1, SkewHermitianParts.dOp_zero, smul_zero, add_zero]
  have e₂ : ecOp π₂ X = dOp π₂ X := by
    unfold ecOp
    rw [SkewHermitianParts.hpart1_skew hX.1.1, SkewHermitianParts.hpart2_skew hX.1.1, SkewHermitianParts.dOp_zero, smul_zero, add_zero]
  rw [← e₁, ← e₂]
  exact hsum.2

theorem intertwiner_group_of_EB : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [FiniteDimensional ℂ V₂] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π₁ : Mx k r → (V₁ →L[ℂ] V₁)) (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (T : V₁ →ₗ[ℂ] V₂) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → IsRepW k r z π₁ → IsRepW k r z π₂ → IsFrameOf k r [z] B → (∀ a b v, T (EB π₁ B a b v) = EB π₂ B a b (T v)) → ∀ h ∈ UWset k r z, ∀ v, T (π₁ h v) = π₂ h (T v) := by
  intro V₁ _ _ _ V₂ _ _ _ k r z π₁ π₂ T B hz hTz h₁ h₂ hB hT h hh
  have hzz : herm (Hpk k r) z z ≠ 0 := by
    rw [Qx8.herm_self']
    intro h0
    rw [neg_eq_zero, Complex.ofReal_eq_zero] at h0
    exact hTz.ne' h0
  refine (exp_generates k r z hz hTz (fun h => h ∈ UWset k r z ∧ ∀ v, T (π₁ h v) = π₂ h (T v))
    ⟨Qx8.uw_one z, fun v => ?_⟩ ?_ h hh).2
  · rw [h₁.1.1, h₂.1.1]
    rfl
  · intro X g hX hg
    have e0 : NormedSpace.exp X ∈ UWset k r z := by
      have := exp_uw hX 1
      simpa using this
    have e₁ : π₁ (NormedSpace.exp X) = NormedSpace.exp (dOp π₁ X) := by
      have := representation_exp V₁ k r z π₁ h₁ X hX 1
      simpa using this
    have e₂ : π₂ (NormedSpace.exp X) = NormedSpace.exp (dOp π₂ X) := by
      have := representation_exp V₂ k r z π₂ h₂ X hX 1
      simpa using this
    refine ⟨SkewHermitianParts.uw_mul e0 hg.1, fun v => ?_⟩
    rw [h₁.1.2 _ e0 _ hg.1, h₂.1.2 _ e0 _ hg.1, e₁, e₂]
    show T (NormedSpace.exp (dOp π₁ X) (π₁ g v)) = NormedSpace.exp (dOp π₂ X) (π₂ g (T v))
    rw [intertwiner_exp_of_intertwiner T (intertwiner_dOp_of_EB T hz hzz h₁ h₂ hB hT hX), hg.2]

end GlobalTheory
