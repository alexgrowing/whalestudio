import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PeriodsLactSymplectic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DblZMemHn
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionSpec
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MapConjInv
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaSummableAndDeterminesTestFn
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinearStatement

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

private theorem kZero_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}
    (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom)
    (h₂ : x₂ ∈ X.dom) (z₁ w : Fin n → Fin g → ℂ) : kZero X idx x₁ x₂ z₁ w ≠ 0 := by
  unfold kZero
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => mul_ne_zero ?_ (Complex.exp_ne_zero _)
  exact inv_ne_zero (pow_ne_zero _ (mul_ne_zero (DblPoint.det_aLin_ne_zero h₁ h₂ τ)
    (DblPoint.det_aAnti_ne_zero h₁ h₂ τ)))

private theorem isUn_one' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) : IsUn X (1 : GL (Fin r) E) := by
  unfold IsUn
  intro x y
  simp

theorem eisTerm_graph : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ γ : GL (Fin r) E, IsUn X γ → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, ∀ z₁ w : Fin n → Fin g → ℂ, kZero X idx x₁ x₂ z₁ w * eisTerm X.Ψ (iota X 1 γ) (dbl X bas idx φ₁ φ₂) (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w) = dbl X bas idx φ₁ (wG X bas idx γ φ₂) 0 * kZero X idx x₁ (lact γ x₂) z₁ w := by
  intro E _ _ _ r X g bas idx n hs hn γ hγ φ₁ φ₂ h₁ h₂ x₁ hx₁ x₂ hx₂ z₁ w

  obtain ⟨hsb₂, hth₂, -⟩ := wG_laws E r X g bas idx n hs hn γ hγ φ₂ h₂
  have hγx₂ : lact γ x₂ ∈ X.dom := IsUn.lact_mem hγ hx₂
  obtain ⟨hT, hZ', -⟩ := dblZ_mem_Hn E r X x₁ hx₁ (lact γ x₂) hγx₂
  have hZ : dblZ X x₁ x₂ ∈ Hn X.Ψ r := (dblZ_mem_Hn E r X x₁ hx₁ x₂ hx₂).2.1

  obtain ⟨hU, a, ha, hact⟩ := iota_act_dbl E r X g bas idx n hs hn 1 γ (isUn_one' X) hγ
  obtain ⟨hA, hzz⟩ := hact x₁ hx₁ x₂ hx₂
  have e1 : lact (1 : GL (Fin r) E) x₁ = x₁ := UnAct.lact_one' x₁
  simp only [e1] at hA hzz

  obtain ⟨hΦ, hΦd, -⟩ := DblEx.dbl_spec E r X g bas idx n hs hn φ₁ φ₂ h₁ h₂
  obtain ⟨hΦ', hΦ'd, -⟩ :=
    DblEx.dbl_spec E r X g bas idx n hs hn φ₁ (wG X bas idx γ φ₂) h₁ hsb₂
  obtain ⟨hW, hWT, -⟩ := GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E X.Ψ hT n r hn (iota X 1 γ) hU (dbl X bas idx φ₁ φ₂) hΦ

  have key : ∀ u v : Fin n → Fin g → ℂ,
      thH X.Ψ (weil X.Ψ (iota X 1 γ) (dbl X bas idx φ₁ φ₂)) (dblZ X x₁ (lact γ x₂))
          (dblz X idx x₁ (lact γ x₂) u v) (dblz' X idx x₁ (lact γ x₂) u v) =
        a * thH X.Ψ (dbl X bas idx φ₁ (wG X bas idx γ φ₂)) (dblZ X x₁ (lact γ x₂))
          (dblz X idx x₁ (lact γ x₂) u v) (dblz' X idx x₁ (lact γ x₂) u v) := by
    intro u v
    obtain ⟨hz, hz', hk⟩ := hzz u v
    have d1 := hΦd x₁ hx₁ x₂ hx₂ u v
    have d2 := hΦ'd x₁ hx₁ (lact γ x₂) hγx₂ u v
    have t2 : thA X bas idx (wG X bas idx γ φ₂) (lact γ x₂) = thA X bas idx φ₂ x₂ :=
      hth₂ x₂ hx₂
    rw [t2, d1] at d2
    have tw := hWT (dblZ X x₁ x₂) hZ (dblz X idx x₁ x₂ u v) (dblz' X idx x₁ x₂ u v)
    rw [hA, ← hz, ← hz'] at tw
    have hK' := kZero_ne_zero X idx hx₁ hγx₂ u v
    apply mul_left_cancel₀ hK'
    rw [tw, ← mul_assoc, hk, mul_assoc, d2]
    ring

  have hW' : weil X.Ψ (iota X 1 γ) (dbl X bas idx φ₁ φ₂) =
      a • dbl X bas idx φ₁ (wG X bas idx γ φ₂) := by
    refine (thH_summable_and_inj E X.Ψ hT n r _ hW _ hZ').2 _ ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ hΦ' hΦ').2.1 a) ?_
    intro z z'
    obtain ⟨u, v, rfl, rfl⟩ := DblEx.dblz_surj E r X g idx n x₁ hx₁ (lact γ x₂) hγx₂ z z'
    rw [key u v]
    unfold thH
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [tsum_mul_left]

  obtain ⟨-, -, hk⟩ := hzz z₁ w
  have hK := kZero_ne_zero X idx hx₁ hx₂ z₁ w
  have hH : hFac X.Ψ (iota X 1 γ) (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z₁ w)
      (dblz' X idx x₁ x₂ z₁ w) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hk
    exact mul_ne_zero ha hK hk.symm
  unfold eisTerm
  rw [hW', Pi.smul_apply, smul_eq_mul, ← mul_inv_cancel_right₀ hH
    (kZero X idx x₁ (lact γ x₂) z₁ w), hk]
  field_simp

end GlobalTheory.SW
