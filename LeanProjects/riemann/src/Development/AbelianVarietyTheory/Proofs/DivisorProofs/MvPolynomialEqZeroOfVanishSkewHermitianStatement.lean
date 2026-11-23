import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPolynomialEqZeroOfVanishSkewHermitian
import Mathlib
import Formalism.SatakeDualWeyl.Statement
set_option autoImplicit false
noncomputable section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPolynomial_eq_zero_of_vanish_skewHermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → σ ≠ AlgHom.id F E → Module.finrank F E = 2 →
    ∀ {ι : Type} [Fintype ι] (ψ : ι → (E →+* ℂ)), Function.Injective (fun τ => (ψ τ).comp (algebraMap F E)) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Formalism.UG.cT (σ : E →+* E) J = J → J.det ≠ 0 →
    ∀ Q : MvPolynomial (ι × Fin n × Fin n) ℂ,
      (∀ S : Matrix (Fin n) (Fin n) E, Formalism.UG.cT (σ : E →+* E) S * J + J * S = 0 →
        MvPolynomial.eval (fun p => ψ p.1 (S p.2.1 p.2.2)) Q = 0) → Q = 0 := by
  first | exact @GlobalTheory.SkewDense.eq_zero_of_vanish_skew | exact GlobalTheory.SkewDense.eq_zero_of_vanish_skew | (intros; apply GlobalTheory.SkewDense.eq_zero_of_vanish_skew <;> assumption)
