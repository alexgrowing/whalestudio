import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensMuF

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def sigE (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) : E ≃ₐ[F] E :=
  AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)

theorem trace_sigR (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (t : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ t) = Algebra.trace R (R ⊗[F] E) t := by
  have h : sigR R σ t = Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) (sigE σ hσ) t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR, sigE]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [h, Algebra.trace_eq_of_algEquiv]

theorem hR_swap (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → R ⊗[F] E) :
    hR R σ J y x = sigR R σ (hR R σ J x y) := by
  have h := gramR_memP R σ hσ J hJ ![x, y] 0 1
  simp only [gramR, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [← h, sigR_invP R σ hσ]

end Gen

theorem BR_symm {D : D7} (X : HidaSetting D) (x y : TupI X) :
    BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y = BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y x := by
  simp only [BR]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hR_swap (Ainf X.B.I.F) X.B.I.cm.sig (sig_invI X) X.B.I.J (J_hermI X) (x a) (y a),
    trace_sigR (Ainf X.B.I.F) X.B.I.cm.sig (sig_invI X)]

theorem betaSym_holds : BetaSym := by
  intro D X x y
  simp only [betaI]
  rw [BR_symm]

end PI.AprimeInfW
