import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianHeisenbergOperatorLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionSpecStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledThetaTestFunctionSesquilinearHeisenbergStatement

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

namespace DblVan

theorem vecMul_inv_inl {E : Type} [Field E] {N : ℕ} {γ : M2 E N} (hγ : IsUnit γ.det)
    {u : Fin N ⊕ Fin N → E} (hu : u ∈ botSpan γ) (a : Fin N) : (u ᵥ* γ⁻¹) (Sum.inl a) = 0 := by
  change u ∈ Submodule.span E (Set.range fun b : Fin N => γ (Sum.inr b)) at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx

    have hrow : (γ (Sum.inr b) ᵥ* γ⁻¹) (Sum.inl a) = (γ * γ⁻¹) (Sum.inr b) (Sum.inl a) := rfl
    rw [hrow, Matrix.mul_nonsing_inv γ hγ, Matrix.one_apply_ne (by simp)]
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_vecMul, Pi.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [Matrix.smul_vecMul, Pi.smul_apply, hx, smul_zero]

theorem heisH_zero_apply_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
    (b : Matrix (Fin n) (Fin N) E) (ψ : Matrix (Fin n) (Fin N) E → ℂ) : heisH 0 b ψ 0 = ψ 0 := by
  simp [heisH, cc]

theorem toCols_eq_zero {E : Type} [Field E] {n N : ℕ} {γ T : M2 E N} (hγ : IsUnit γ.det)
    {ξ : Fin N → E} (hu : Sum.elim ξ 0 ᵥ* T ∈ botSpan γ) (v : Fin n → E) :
    (Matrix.fromCols (vecMulVec v ξ) (0 : Matrix (Fin n) (Fin N) E) * T * γ⁻¹).toCols₁ = 0 := by
  ext k a
  rw [Matrix.toCols₁_apply, Matrix.zero_apply]

  have hrow : (Matrix.fromCols (vecMulVec v ξ) (0 : Matrix (Fin n) (Fin N) E) * T) k =
      v k • (Sum.elim ξ 0 ᵥ* T) := by
    ext j
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fintype.sum_sum_type, vecMulVec_apply,
      Finset.mul_sum, mul_assoc]
  have hentry : (Matrix.fromCols (vecMulVec v ξ) (0 : Matrix (Fin n) (Fin N) E) * T * γ⁻¹) k
      (Sum.inl a) = ((v k • (Sum.elim ξ 0 ᵥ* T)) ᵥ* γ⁻¹) (Sum.inl a) := by
    rw [← hrow]; rfl
  rw [hentry]
  exact vecMul_inv_inl hγ (Submodule.smul_mem _ _ hu) a

end DblVan

open DblVan in

theorem weil_dbl_zero_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → ∀ ξ : Fin r → E, (∃ (s : Finset (Fin n → E)) (a : (Fin n → E) → ℂ), ∑ v ∈ s, a v ≠ 0 ∧ ∑ v ∈ s, a v • heisG X bas (vecMulVec v ξ) φ₁ = 0) → ∀ γ ∈ UU E r, Sum.elim ξ 0 ᵥ* dblT X ∈ botSpan γ → weil X.Ψ γ (dbl X bas idx φ₁ φ₂) 0 = 0 := by
  intro E _ _ _ r X g bas idx n hs hn φ₁ φ₂ h₁ h₂ ξ hker γ hγ hξ
  obtain ⟨s, a, hsum, hkill⟩ := hker
  have hΨ : IsType X.Ψ := X.cmType
  have hγu : IsUnit γ.det := (HAct.group_part hγ).1

  have hSBd : ∀ ψ : TF n g, IsSB ψ → IsSB (dbl X bas idx ψ φ₂) := fun ψ hψ =>
    (GlobalTheory.T.doubledHermitianTestFunction_spec E r X g bas idx n hs hn ψ φ₂ hψ h₂).1
  have hΦ := hSBd φ₁ h₁
  have hG := (heisG_laws E r X g bas idx n hs hn).2.2.2
  have hwadd : ∀ f f' : Matrix (Fin n) (Fin r) E → ℂ, IsSB f → IsSB f' →
      weil X.Ψ γ (f + f') = weil X.Ψ γ f + weil X.Ψ γ f' := fun f f' hf hf' =>
    ((GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E X.Ψ hΨ n r hn γ hγ f hf).2.2.2.1 f' hf').2
  have hwsmul : ∀ (c : ℂ) (f : Matrix (Fin n) (Fin r) E → ℂ), IsSB f →
      weil X.Ψ γ (c • f) = c • weil X.Ψ γ f := fun c f hf =>
    (GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E X.Ψ hΨ n r hn γ hγ f hf).2.2.2.2.1 c

  have hdbl0 : dbl X bas idx (0 : TF n g) φ₂ = 0 := by
    have h := (GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hn φ₁ φ₂ h₁ h₂).2.1 0 1
    rwa [zero_smul, one_smul, zero_mul, zero_smul] at h
  have hw0 : weil X.Ψ γ (0 : Matrix (Fin n) (Fin r) E → ℂ) = 0 := by
    have h := hwsmul 0 _ hΦ
    rwa [zero_smul, zero_smul] at h

  have hone : ∀ v : Fin n → E, weil X.Ψ γ (dbl X bas idx (heisG X bas (vecMulVec v ξ) φ₁) φ₂) 0 =
      weil X.Ψ γ (dbl X bas idx φ₁ φ₂) 0 := by
    intro v
    have h3 := (GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hn φ₁ φ₂ h₁ h₂).2.2 (vecMulVec v ξ) 0
    rw [(hG 0 φ₂ h₂).2.1] at h3
    rw [h3, (GlobalTheory.T.hermitianHeisenbergOperator_laws E X.Ψ hΨ n r hn _ _ _ hΦ).2.2 γ hγ, Matrix.fromCols_toCols,
      DblVan.toCols_eq_zero hγu hξ v, DblVan.heisH_zero_apply_zero]

  have hlin : ∀ t : Finset (Fin n → E),
      IsSB (∑ v ∈ t, a v • heisG X bas (vecMulVec v ξ) φ₁) ∧
      weil X.Ψ γ (dbl X bas idx (∑ v ∈ t, a v • heisG X bas (vecMulVec v ξ) φ₁) φ₂) =
        ∑ v ∈ t, a v • weil X.Ψ γ (dbl X bas idx (heisG X bas (vecMulVec v ξ) φ₁) φ₂) := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨isSB_zero, by rw [Finset.sum_empty, Finset.sum_empty, hdbl0, hw0]⟩
    | insert w t hw ih =>
      obtain ⟨hS, hval⟩ := ih
      have hGw := (hG (vecMulVec w ξ) φ₁ h₁).1
      have hcGw := (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) _ _ hGw hGw).2.1 (a w)
      rw [Finset.sum_insert hw, Finset.sum_insert hw]
      refine ⟨(isSB_algebra_haar_linear ℚ (Fin n) (Fin g) _ _ hcGw hS).1, ?_⟩
      have hI := GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hn _ φ₂ hcGw h₂
      have hJ := GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hn _ φ₂ hGw h₂
      have hsm : dbl X bas idx (a w • heisG X bas (vecMulVec w ξ) φ₁) φ₂ =
          a w • dbl X bas idx (heisG X bas (vecMulVec w ξ) φ₁) φ₂ := by
        have h := hJ.2.1 (a w) 1
        rwa [one_smul, map_one, mul_one] at h
      rw [(hI.1 _ hS).1, hwadd _ _ (hSBd _ hcGw) (hSBd _ hS), hval, hsm,
        hwsmul _ _ (hSBd _ hGw)]

  have hmain := (hlin s).2
  rw [hkill, hdbl0, hw0] at hmain
  have h0 := congrFun hmain 0
  simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hone,
    ← Finset.sum_mul] at h0
  exact (mul_eq_zero.mp h0.symm).resolve_left hsum

end GlobalTheory.SW
