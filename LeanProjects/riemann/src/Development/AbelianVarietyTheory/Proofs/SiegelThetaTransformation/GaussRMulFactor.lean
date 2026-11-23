import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPeriodMapHomeomorphRiemannFormDensityStatement

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker.RealHeis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)

theorem hx_add_left (z z' w : Fin g → ℂ) :
    hx X bas idx x (z + z') w = hx X bas idx x z w + hx X bas idx x z' w := by
  simp only [GlobalTheory.Dict.hx, mulVec_add, add_dotProduct]

theorem hx_add_right (z w w' : Fin g → ℂ) :
    hx X bas idx x z (w + w') = hx X bas idx x z w + hx X bas idx x z w' := by
  simp only [GlobalTheory.Dict.hx, mulVec_add, star_add, dotProduct_add]

theorem hx_smul_left (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x (c • z) w = c * hx X bas idx x z w := by
  simp only [GlobalTheory.Dict.hx, mulVec_smul, smul_dotProduct, smul_eq_mul]

theorem contDiff_gaussR : ContDiff ℝ (⊤ : ℕ∞) (gaussR X bas idx x : (Fin n → Fin g → ℂ) → ℂ) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => star z) := Complex.conjCLE.contDiff
  have h1 : ∀ (k : Fin n) (i : Fin g), ContDiff ℝ (⊤ : ℕ∞)
      fun z : Fin n → Fin g → ℂ => (hMat X bas idx x *ᵥ z k) i := by
    intro k i
    simp only [mulVec, dotProduct]
    fun_prop
  have h2 : ∀ k : Fin n, ContDiff ℝ (⊤ : ℕ∞)
      fun z : Fin n → Fin g → ℂ => hx X bas idx x (z k) (z k) := by
    intro k
    change ContDiff ℝ _ fun z : Fin n → Fin g → ℂ => ∑ i, (hMat X bas idx x *ᵥ z k) i *
      ∑ j, imInv X bas idx x i j * star ((hMat X bas idx x *ᵥ z k) j)
    exact ContDiff.sum fun i _ => (h1 k i).mul
      (ContDiff.sum fun j _ => contDiff_const.mul (hc.comp (h1 k j)))
  exact (contDiff_const.mul (ContDiff.sum fun k _ => h2 k)).neg.cexp

theorem gaussR_mul_factor (hsym : ∀ z w, hx X bas idx x w z = conj (hx X bas idx x z w))
    (z a : Fin n → Fin g → ℂ) :
    gaussR X bas idx x z * cexp (-(π * ∑ k, hx X bas idx x (z k + (1 / 2 : ℂ) • a k) (a k))) =
      cexp (-(π * I * ((∑ k, hx X bas idx x (z k) (a k)).im : ℝ))) * gaussR X bas idx x (z + a) := by
  have h1 : ∑ k, hx X bas idx x (a k) (z k) = conj (∑ k, hx X bas idx x (z k) (a k)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hsym _ _
  simp only [gaussR, ← Complex.exp_add, Pi.add_apply, hx_add_left, hx_add_right, hx_smul_left,
    Finset.sum_add_distrib, ← Finset.mul_sum, h1]
  congr 1
  generalize ∑ k, hx X bas idx x (z k) (a k) = S
  have h2 := Complex.sub_conj S
  push_cast at h2
  linear_combination (-(π : ℂ) / 2) * h2

end GlobalTheory.Ker.RealHeis

namespace GlobalTheory.Ker

theorem thR_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, ∀ φ : TF n g, IsSB φ → ContDiff ℝ (⊤ : ℕ∞) (thR X bas idx φ x : WR X n → ℂ) ∧ (∀ (y : Matrix (Fin n) (Fin r) E) (v : WR X n), thR X bas idx (heisG X bas y φ) x v = cexp (-(π * I * (EFR X v (embR X y) : ℝ))) * thR X bas idx φ x (v + embR X y)) ∧ (∀ γ : GL (Fin r) E, IsUn X γ → ∀ v : WR X n, thR X bas idx (wG X bas idx γ φ) (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) = thR X bas idx φ x v) ∧ (∀ ψ, IsSB ψ → (thR X bas idx φ x = (thR X bas idx ψ x : WR X n → ℂ) → φ = ψ) ∧ thR X bas idx (φ + ψ) x = (thR X bas idx φ x + thR X bas idx ψ x : WR X n → ℂ)) ∧ ∀ a : ℂ, thR X bas idx (a • φ) x = (a • thR X bas idx φ x : WR X n → ℂ) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn x hxd φ hφ
  obtain ⟨⟨L, hL⟩, him, -, -, hinv⟩ := GlobalTheory.T.realPeriodMap_homeomorph_riemannForm_density E r X g q0 hr bas idx n hs hn x hxd
  obtain ⟨hsym, -, -, -, -, -, -, hga⟩ := GlobalTheory.Dict.hx_laws E r X g bas idx n hs hn x hxd
  have hLf : zR X idx x = (L : WR X n → Fin n → Fin g → ℂ) := funext fun v => (hL v).symm
  refine ⟨?_, fun y v => ?_, fun γ hγ v => ?_, fun ψ hψ => ⟨fun h => ?_, ?_⟩, fun a => ?_⟩
  · have h1 : ContDiff ℝ (⊤ : ℕ∞) (thA X bas idx φ x) :=
      (AnalyticOnNhd.contDiff (𝕜 := ℂ) (SCV.analyticOnNhd_of_differentiable
        (ThetaHol.differentiable_thA idx hs hφ hxd) _)).restrict_scalars ℝ
    have h2 := ((RealHeis.contDiff_gaussR X bas idx x).mul h1).comp L.contDiff
    rw [← hLf] at h2
    exact h2
  · have h1 := ((heisG_laws E r X g bas idx n hs hn).2.2.2 y φ hφ).2.2.2.2 x hxd (zR X idx x v)
    have h2 : zR X idx x (v + embR X y) = zR X idx x v + zR X idx x (embR X y) := by
      rw [hLf, map_add]
    have h3 := RealHeis.gaussR_mul_factor X bas idx x hsym (zR X idx x v) (zR X idx x (embR X y))
    rw [him] at h3
    rw [thR, thR, h1, h2, ← _root_.mul_assoc, ← _root_.mul_assoc, ← h3]
    rfl
  · rw [thR, thR, hinv γ hγ v, (wG_laws E r X g bas idx n hs hn γ hγ φ hφ).2.1 x hxd]
    simp only [gaussR, (hga γ hγ).2.2.2]
  · have hone : IsUn X (1 : GL (Fin r) E) := fun u w => by simp
    refine ((wG_laws E r X g bas idx n hs hn 1 hone φ hφ).2.2.1 ψ hψ).2.2 x hxd ?_
    funext z
    obtain ⟨v, rfl⟩ := L.surjective z
    have h1 := congrFun h v
    rw [thR, thR, ← hL] at h1
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) h1
  · funext v
    simp only [thR, UnAct.thA_add idx hs hxd hφ hψ, Pi.add_apply, mul_add]
  · funext v
    simp only [thR, UnAct.thA_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]

end GlobalTheory.Ker
