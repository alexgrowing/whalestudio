import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledThetaTestFunctionSesquilinearHeisenberg
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockHxDifferentiable
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPeriodMapHomeomorphRiemannFormDensityStatement

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker.Diag

open GlobalTheory.SW.DblLin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

variable (X) in

noncomputable def kRow (x₁ x₂ : Frame X.Ψ r) (z w : Fin g → ℂ) : ℂ :=
  ∑ τ, cz' X idx x₁ x₂ τ (z, w) ⬝ᵥ (imH (dblZ X x₁ x₂ τ))⁻¹ *ᵥ cz X idx x₁ x₂ τ (z, w)

theorem kZero_eq (x₁ x₂ : Frame X.Ψ r) (z w : Fin n → Fin g → ℂ) :
    kZero X idx x₁ x₂ z w =
      (∏ τ : X.Ψ, (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹) *
        cexp (π * ∑ k, kRow X idx x₁ x₂ (z k) (w k)) := by
  simp only [kZero, Finset.prod_mul_distrib, ← Complex.exp_sum, ← Finset.mul_sum, kRow]
  rw [Finset.sum_comm]
  rfl

theorem kRow_per (hs : IsSympl X bas) {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom)
    (y : Fin r → E) (z z' : Fin g → ℂ) :
    kRow X idx x₁ x₂ (pv X idx x₁ y + z) (fun i => conj ((pv X idx x₂ y + z') i)) =
      hx X bas idx x₁ (z + (1 / 2 : ℂ) • pv X idx x₁ y) (pv X idx x₁ y) +
      conj (hx X bas idx x₂ (z' + (1 / 2 : ℂ) • pv X idx x₂ y) (pv X idx x₂ y)) +
      kRow X idx x₁ x₂ z (fun i => conj (z' i)) := by
  have h := expo_row idx hs h₁ h₂ y y z (star z')
  have e0 : ∀ τ : X.Ψ, Data.emb τ.1 (0 : Fin r → E) = 0 := fun τ => by
    funext a; simp [Data.emb]
  have e1 : (fun i => conj ((pv X idx x₂ y + z') i)) = star z' + star (per X x₂ y ∘ idx) := by
    funext i; simp [pv, add_comm]
  rw [e1, add_comm (pv X idx x₁ y) z]
  simp only [sub_self, e0, star_zero, zero_dotProduct, dotProduct_zero, add_zero,
    Finset.sum_const_zero, mul_zero, Pi.zero_apply, star_star, hermForm_Hm] at h
  simp only [cc, map_zero, mul_zero, Finset.sum_const_zero, Rat.cast_zero, add_zero] at h
  exact h

theorem continuous_kRow (x₁ x₂ : Frame X.Ψ r) :
    Continuous fun p : (Fin g → ℂ) × (Fin g → ℂ) => kRow X idx x₁ x₂ p.1 p.2 := by
  refine continuous_finsetSum _ fun τ _ => ?_
  exact (cz' X idx x₁ x₂ τ).continuous_of_finiteDimensional.dotProduct
    (continuous_const.matrix_mulVec (cz X idx x₁ x₂ τ).continuous_of_finiteDimensional)

theorem continuous_hx (x : Frame X.Ψ r) :
    Continuous fun z : Fin g → ℂ => hx X bas idx x z z :=
  (continuous_const.matrix_mulVec continuous_id).dotProduct
    (continuous_const.matrix_mulVec (continuous_const.matrix_mulVec continuous_id).star)

theorem kernel_diag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, ∀ a b w : WR X n, cexp (π * I * (EFR X w (a - b) : ℝ)) * (gaussR X bas idx x₁ (zR X idx x₁ (w + a)) * conj (gaussR X bas idx x₂ (zR X idx x₂ (w + b))) * kZero X idx x₁ x₂ (zR X idx x₁ (w + a)) (fun k i => conj (zR X idx x₂ (w + b) k i))) = gaussR X bas idx x₁ (zR X idx x₁ a) * conj (gaussR X bas idx x₂ (zR X idx x₂ b)) * kZero X idx x₁ x₂ (zR X idx x₁ a) (fun k i => conj (zR X idx x₂ b k i)) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn x₁ h₁ x₂ h₂ a b w
  obtain ⟨⟨L₁, hL₁⟩, im₁, -, hd, -⟩ := GlobalTheory.T.realPeriodMap_homeomorph_riemannForm_density E r X g q0 hr bas idx n hs hn x₁ h₁
  obtain ⟨⟨L₂, hL₂⟩, im₂, -⟩ := GlobalTheory.T.realPeriodMap_homeomorph_riemannForm_density E r X g q0 hr bas idx n hs hn x₂ h₂
  have add₁ (u v : WR X n) : zR X idx x₁ (u + v) = zR X idx x₁ u + zR X idx x₁ v := by
    rw [← hL₁, ← hL₁, ← hL₁, map_add]
  have add₂ (u v : WR X n) : zR X idx x₂ (u + v) = zR X idx x₂ u + zR X idx x₂ v := by
    rw [← hL₂, ← hL₂, ← hL₂, map_add]
  have hE (w : WR X n) : EFR X w (a - b) = EFR X w a - EFR X w b := by
    rw [← im₁, ← im₁, ← im₁, ← sub_im, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eq_sub_iff_add_eq, ← GlobalTheory.Dict.fock_hx_add_right, ← Pi.add_apply (zR X idx x₁ (a - b)),
      ← add₁, sub_add_cancel]
  have key : ∀ w : WR X n, π * I * (EFR X w (a - b) : ℝ) +
      (-(π / 2 * ∑ k, hx X bas idx x₁ (zR X idx x₁ (w + a) k) (zR X idx x₁ (w + a) k)) +
        conj (-(π / 2 * ∑ k, hx X bas idx x₂ (zR X idx x₂ (w + b) k) (zR X idx x₂ (w + b) k))) +
        π * ∑ k, kRow X idx x₁ x₂ (zR X idx x₁ (w + a) k) (fun i => conj (zR X idx x₂ (w + b) k i))) =
      -(π / 2 * ∑ k, hx X bas idx x₁ (zR X idx x₁ a k) (zR X idx x₁ a k)) +
        conj (-(π / 2 * ∑ k, hx X bas idx x₂ (zR X idx x₂ b k) (zR X idx x₂ b k))) +
        π * ∑ k, kRow X idx x₁ x₂ (zR X idx x₁ a k) (fun i => conj (zR X idx x₂ b k i)) := by
    intro w
    refine hd.induction_on w (isClosed_eq ?_ continuous_const) fun y => ?_
    · have c₁ (k) : Continuous fun w : WR X n => zR X idx x₁ (w + a) k := by
        simp only [← hL₁]; fun_prop
      have c₂ (k) : Continuous fun w : WR X n => zR X idx x₂ (w + b) k := by
        simp only [← hL₂]; fun_prop
      have c₃ : Continuous fun w : WR X n => EFR X w (a - b) := by
        unfold EFR hermC; fun_prop
      have c₄ := continuous_finsetSum Finset.univ fun k _ =>
        (continuous_hx (bas := bas) idx x₁).comp (c₁ k)
      have c₅ := continuous_finsetSum Finset.univ fun k _ =>
        (continuous_hx (bas := bas) idx x₂).comp (c₂ k)
      have c₆ := continuous_finsetSum Finset.univ fun k _ =>
        (continuous_kRow idx x₁ x₂).comp ((c₁ k).prodMk (c₂ k).star)
      exact (continuous_const.mul (continuous_ofReal.comp c₃)).add
        (((continuous_const.mul c₄).neg.add
          (continuous_conj.comp (continuous_const.mul c₅).neg)).add (continuous_const.mul c₆))
    · have i₁ := sub_conj (∑ k, hx X bas idx x₁ (zR X idx x₁ (embR X y) k) (zR X idx x₁ a k))
      have i₂ := sub_conj (∑ k, hx X bas idx x₂ (zR X idx x₂ (embR X y) k) (zR X idx x₂ b k))
      rw [im₁] at i₁
      rw [im₂] at i₂
      rw [hE, add₁, add₂]
      simp only [Pi.add_apply (zR X idx _ (embR X y)), zR_embR] at i₁ i₂ ⊢
      simp only [kRow_per idx hs h₁ h₂]
      have s₁ (k) := GlobalTheory.Dict.fock_hx_conj X bas idx x₁ hs h₁ (pv X idx x₁ (y k)) (zR X idx x₁ a k)
      have s₂ (k) := GlobalTheory.Dict.fock_hx_conj X bas idx x₂ hs h₂ (pv X idx x₂ (y k)) (zR X idx x₂ b k)
      simp only [GlobalTheory.Dict.fock_hx_add_left, GlobalTheory.Dict.fock_hx_add_right, GlobalTheory.Dict.fock_hx_smul_left,
        s₁, s₂, Finset.sum_add_distrib, ← Finset.mul_sum, ← map_sum, map_add, map_mul, map_neg,
        conj_conj, map_div₀, conj_ofReal, map_ofNat, map_one]
      push_cast at i₁ i₂ ⊢
      linear_combination (-(π : ℂ) / 2) * i₁ + ((π : ℂ) / 2) * i₂
  simp only [gaussR, kZero_eq, ← Complex.exp_conj]
  have := congrArg cexp (key w)
  simp only [Complex.exp_add] at this
  linear_combination (∏ τ : X.Ψ, (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹) * this

end GlobalTheory.Ker.Diag
