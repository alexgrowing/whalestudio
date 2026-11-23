import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GardingVectorDerivativeEqGardingVectorStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVecLinear

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin n → Bool} {G : Matrix (Fin n) (Fin n) ℂ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem lieG_add {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (hY : Y ∈ lieG G) : X + Y ∈ lieG G := by
  have h1 : Xᴴ * G + G * X = 0 := hX
  have h2 : Yᴴ * G + G * Y = 0 := hY
  show (X + Y)ᴴ * G + G * (X + Y) = 0
  rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, h1, h2, add_zero]

theorem lieG_smul (a : ℝ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) : a • X ∈ lieG G := by
  have h1 : Xᴴ * G + G * X = 0 := hX
  show (a • X)ᴴ * G + G * (a • X) = 0
  rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]

theorem gard_add (hσ : IsURepOn (UJset ε) σ) {φ ψ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (hψ : IsTest ψ)
    (w : H) : gard ε σ (φ + ψ) w = gard ε σ φ w + gard ε σ ψ w := by
  unfold gard
  rw [← integral_add (hφ.integrable (continuous_orbit hσ w)) (hψ.integrable (continuous_orbit hσ w))]
  simp only [Pi.add_apply, add_smul]

theorem gard_smul (a : ℝ) (φ : Matrix (Fin n) (Fin n) ℂ → ℝ) (w : H) :
    gard ε σ (a • φ) w = (a : ℂ) • gard ε σ φ w := by
  unfold gard
  rw [← integral_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Complex.coe_smul]

theorem dRep_linear : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ w ∈ smSub G (trRep σ P), (∀ X ∈ lieG G, ∀ Y ∈ lieG G, dRep (trRep σ P) (X + Y) w = dRep (trRep σ P) X w + dRep (trRep σ P) Y w) ∧ ∀ (a : ℝ), ∀ X ∈ lieG G, dRep (trRep σ P) (a • X) w = (a : ℂ) • dRep (trRep σ P) X w := by
  intro n ε H _ _ _ σ P G hP h hσ w hw
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  refine ⟨fun X hX Y hY => ?_, fun a X hX => ?_⟩
  · refine sub_eq_zero.1 (eq_zero_of_inner_gard hσ fun φ hφ v => ?_)
    obtain ⟨ψ, hψ⟩ := GlobalTheory.T.gardingVector_derivative_eq_gardingVector n ε H σ P G hP h hσ φ hφ
    have hu := gard_mem hP h hσ hφ v
    rw [inner_sub_right, inner_add_right, inner_dRep hG hπ hu hw hX, inner_dRep hG hπ hu hw hY,
      inner_dRep hG hπ hu hw (lieG_add hX hY), (hψ X).2 hX, (hψ Y).2 hY, (hψ _).2 (lieG_add hX hY), map_add,
      gard_add hσ (hψ X).1 (hψ Y).1, inner_add_left]
    ring
  · refine sub_eq_zero.1 (eq_zero_of_inner_gard hσ fun φ hφ v => ?_)
    obtain ⟨ψ, hψ⟩ := GlobalTheory.T.gardingVector_derivative_eq_gardingVector n ε H σ P G hP h hσ φ hφ
    have hu := gard_mem hP h hσ hφ v
    rw [inner_sub_right, inner_smul_right, inner_dRep hG hπ hu hw hX,
      inner_dRep hG hπ hu hw (lieG_smul a hX), (hψ X).2 hX, (hψ _).2 (lieG_smul a hX), map_smul,
      gard_smul, inner_smul_left, Complex.conj_ofReal]
    ring

end GlobalTheory.SmVecLinear
