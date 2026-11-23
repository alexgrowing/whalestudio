import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.HasDerivAtExpReal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorRepresentations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket

open Formalism.REAL Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.CompanionTheory.HolCoef.CapLW

section perm

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

omit [Algebra ℂ A] in
theorem glRel_perm {E : Fin n → Fin n → A} (hE : GlRel E) (σ : Equiv.Perm (Fin n)) :
    GlRel fun a b => E (σ a) (σ b) := by
  intro a b c d
  simpa only [σ.injective.eq_iff] using hE (σ a) (σ b) (σ c) (σ d)

theorem qdet_perm {E : Fin n → Fin n → A} (hE : GlRel E) (σ : Equiv.Perm (Fin n)) (u : ℂ) :
    qdet (fun a b => E (σ a) (σ b)) u = qdet E u := by
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun c a => if c = σ a then 1 else 0
  let Q : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun b d => if d = σ b then 1 else 0
  have hQP : Q * P = 1 := by
    ext b a
    simp [P, Q, Matrix.mul_apply, Matrix.one_apply, eq_comm]
  have h := (Formalism.FourierDecayAlt.P.contractions_covariant A n E P Q hE hQP (mul_eq_one_comm.1 hQP) u 0 0 0 0).1
  rw [← h]
  congr 1
  funext a b
  simp [Formalism.FourierDecayAlt.Q.Econj, P, Q, ite_smul]

end perm

section order

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

end order

end GlobalTheory.CompanionTheory.HolCoef.CapLW
