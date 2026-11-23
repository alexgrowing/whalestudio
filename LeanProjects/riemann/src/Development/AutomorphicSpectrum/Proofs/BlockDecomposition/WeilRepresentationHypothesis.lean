import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RWMulN
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompUnitMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationWhittakerHypothesisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnstatedLocalWeilLemma
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2LocalData.WRepProof

def RightRule {F X : Type} [Field F] (R : Matrix (Fin 2) (Fin 2) F → X → X) (S : Set X)
    (h : Matrix (Fin 2) (Fin 2) F) : Prop :=
  h.det = 1 ∧ ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 → ∀ Φ ∈ S, R (g * h) Φ = R g (R h Φ)

theorem RightRule.mul {F X : Type} [Field F] {R : Matrix (Fin 2) (Fin 2) F → X → X} {S : Set X}
    (hS : ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 → ∀ Φ ∈ S, R g Φ ∈ S)
    {h₁ h₂ : Matrix (Fin 2) (Fin 2) F} (p₁ : RightRule R S h₁) (p₂ : RightRule R S h₂) :
    RightRule R S (h₁ * h₂) := by
  refine ⟨by rw [Matrix.det_mul, p₁.1, p₂.1, one_mul], fun g hg Φ hΦ => ?_⟩
  have hΦ' := hS h₂ p₂.1 Φ hΦ
  rw [← mul_assoc, p₂.2 (g * h₁) (by rw [Matrix.det_mul, hg, p₁.1, one_mul]) Φ hΦ,
    p₁.2 g hg _ hΦ', p₂.2 h₁ p₁.1 Φ hΦ]

theorem rightRule_all {F X : Type} [Field F] {R : Matrix (Fin 2) (Fin 2) F → X → X} {S : Set X}
    (hS : ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 → ∀ Φ ∈ S, R g Φ ∈ S)
    (hN : ∀ b : F, RightRule R S !![1, b; 0, 1])
    (hM : ∀ s : Fˣ, RightRule R S !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)])
    (hW : RightRule R S !![0, 1; -1, 0])
    (h : Matrix (Fin 2) (Fin 2) F) (hh : h.det = 1) : RightRule R S h := by
  have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact hh
  by_cases hc : h 1 0 = 0
  · rw [hc, mul_zero, sub_zero] at hdet
    have h0 : h 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have e : h = !![1, h 0 1 * h 0 0; 0, 1] * !![((Units.mk0 _ h0 : Fˣ) : F), 0; 0, (((Units.mk0 _ h0)⁻¹ : Fˣ) : F)] := by
      have e1 : h 1 1 = (h 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc, e1, h0]
    rw [e]
    exact (hN _).mul hS (hM _)
  · have hs : -(h 1 0)⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hc)
    have e : h = !![1, h 0 0 / h 1 0; 0, 1] *
        (!![((Units.mk0 _ hs : Fˣ) : F), 0; 0, (((Units.mk0 _ hs)⁻¹ : Fˣ) : F)] *
          (!![0, 1; -1, 0] * !![1, h 1 1 / h 1 0; 0, 1])) := by
      have e1 : h 0 1 = (h 0 0 * h 1 1 - 1) / h 1 0 := by
        rw [← hdet]
        field_simp
        ring
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      all_goals first | field_simp | skip
      all_goals first | (rw [e1]; field_simp; ring) | ring
    rw [e]
    exact (hN _).mul hS ((hM _).mul hS (hW.mul hS (hN _)))

end GlobalTheory.CompanionTheory.GL2LocalData.WRepProof

open GlobalTheory.CompanionTheory.GL2LocalData.WRepProof in

theorem GlobalTheory.CompanionTheory.GL2LocalData.wRep : Ad3.K.GL2LocalData.WRep := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη g h hg hh Φ hΦ
  have hS : ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 → ∀ Φ ∈ SBE E, rWE E χ σ η g Φ ∈ SBE E :=
    fun g hg Φ hΦ => (GlobalTheory.CompanionTheory.WeilSB.wsb F χ hχ hχ1 E hfr hcont σ hσ η hη g hg Φ hΦ).1
  have hN : ∀ b : F, RightRule (rWE E χ σ η) (SBE E) !![1, b; 0, 1] := fun b =>
    ⟨by simp [Matrix.det_fin_two], fun g hg Φ hΦ =>
      GlobalTheory.CompanionTheory.GL2LocalData.wRepN F χ hχ hχ1 E hfr hcont σ hσ η hη g hg b Φ hΦ⟩
  have hM : ∀ s : Fˣ, RightRule (rWE E χ σ η) (SBE E) !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)] := fun s =>
    ⟨by simp [Matrix.det_fin_two], fun g hg Φ hΦ =>
      GlobalTheory.CompanionTheory.WeilTorus.wRepM F χ hχ hχ1 E hfr hcont σ hσ η hη g hg s Φ hΦ⟩
  have hW : RightRule (rWE E χ σ η) (SBE E) !![0, 1; -1, 0] :=
    ⟨by simp [Matrix.det_fin_two], fun g hg Φ hΦ =>
      GlobalTheory.T.weil_representation_whittaker_hypothesis F χ hχ hχ1 E hfr hcont σ hσ η hη g hg Φ hΦ⟩
  exact (rightRule_all hS hN hM hW h hh).2 g hg Φ hΦ
