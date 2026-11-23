import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLineDerivativeExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParaSpan
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_line_derivative_exists : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d d₁ : ℕ}
    (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁), H'.x ≠ 0 →
    ∀ γ ∈ Lines σ W, ∀ γ₁ ∈ Lines σ W₁, ∀ t : Multiplicative ℝ →* (AE F E)ˣ, (∀ s, IsLevi H' (t s) (γ₁ s) (γ s)) →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ z : ℝ,
      ∃ c : ℂ, HasDerivAt (fun s : ℝ => (χ (t (Multiplicative.ofAdd s)) : ℂ) *
        (((absE F E (t (Multiplicative.ofAdd s)) : ℝ) ^ z : ℝ) : ℂ)) c 0 := by
  first | exact @GlobalTheory.LeviLineChar.hasDerivAt_levi_char | exact GlobalTheory.LeviLineChar.hasDerivAt_levi_char | (intros; apply GlobalTheory.LeviLineChar.hasDerivAt_levi_char <;> assumption)
