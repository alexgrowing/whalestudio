import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroup
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem exists_isFdeg_smul_of_isDS : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → ∀ c : NNReal, 0 < c → ∃ d : ℝ, IsFdeg ((c : ENNReal) • Formalism.REAL.muG ε) σ d := by
  intro n ε lam H _ _ σ h c hc
  obtain ⟨h1, h2, hU, hirr, hsq, -⟩ := h
  obtain ⟨d, hd, hI⟩ := GlobalTheory.schur_orthogonality_unitary n ε H σ hU hirr hsq
  have hc' : (0 : ℝ) < (c : ℝ) := hc
  refine ⟨d / c, div_pos hd hc', fun v w v' w' => ⟨(hI v w v' w').1.smul_measure ENNReal.coe_ne_top, ?_⟩⟩
  rw [integral_smul_measure, (hI v w v' w').2, ENNReal.coe_toReal, Complex.real_smul,
    Complex.ofReal_div, div_div_eq_mul_div]
  ring

end GlobalTheory.Mem.Vol
