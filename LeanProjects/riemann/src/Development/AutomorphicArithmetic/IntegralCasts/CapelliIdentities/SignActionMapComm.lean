import Mathlib
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.SatakeDualWeyl.Statement
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

theorem UpperTheory.Reformulated.B.Qk24.aux2 :
    ∀ (I : Formalism.MainNotions.S.AutInst), IsFractionRing (NumberField.RingOfIntegers I.F) I.F := by
  intro I
  infer_instance

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk24.VA :
    Formalism.MainNotions.S.AutInst → Type :=
    fun (I : Formalism.MainNotions.S.AutInst) ↦ Fin I.n → TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk24.sigA :
    (I : Formalism.MainNotions.S.AutInst) → TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F) →+* TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F) :=
    fun (I : Formalism.MainNotions.S.AutInst) ↦ Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)

noncomputable def UpperTheory.Reformulated.B.Qk24.colM :
    (I : Formalism.MainNotions.S.AutInst) →
      {k : ℕ} → (Fin k → UpperTheory.Reformulated.B.Qk24.VA I) → Matrix (Fin I.n) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) :=
    fun (I : Formalism.MainNotions.S.AutInst) {k : ℕ} (b : Fin k → UpperTheory.Reformulated.B.Qk24.VA I) ↦
      (Matrix.of :
          (Fin I.n → Fin k → TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) →
            Matrix (Fin I.n) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)))
        fun (l : Fin I.n) (i : Fin k) ↦ b i l

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk24.Jf :
    (I : Formalism.MainNotions.S.AutInst) → Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) :=
    fun (I : Formalism.MainNotions.S.AutInst) ↦ I.J.map (⇑(Formalism.UG.inclE (Formalism.MainNotions.S.Af I.F)) : I.E → TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))

noncomputable def UpperTheory.Reformulated.B.Qk24.rowM :
    (I : Formalism.MainNotions.S.AutInst) →
      {k : ℕ} → (Fin k → UpperTheory.Reformulated.B.Qk24.VA I) → Matrix (Fin k) (Fin I.n) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) :=
    fun (I : Formalism.MainNotions.S.AutInst) {k : ℕ} (b : Fin k → UpperTheory.Reformulated.B.Qk24.VA I) ↦
      Formalism.UG.cT (UpperTheory.Reformulated.B.Qk24.sigA I) (UpperTheory.Reformulated.B.Qk24.colM I b) * UpperTheory.Reformulated.B.Qk24.Jf I

noncomputable def UpperTheory.Reformulated.B.Qk24.Mk :
    (I : Formalism.MainNotions.S.AutInst) →
      {k : ℕ} →
        (Fin k → UpperTheory.Reformulated.B.Qk24.VA I) →
          (Fin k → UpperTheory.Reformulated.B.Qk24.VA I) →
            Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) →
              Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) →
                Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) :=
    fun (I : Formalism.MainNotions.S.AutInst) {k : ℕ} (b d : Fin k → UpperTheory.Reformulated.B.Qk24.VA I)
        (X Y : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) ↦
      (1 : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) +
          UpperTheory.Reformulated.B.Qk24.colM I b * X * UpperTheory.Reformulated.B.Qk24.rowM I d +
        UpperTheory.Reformulated.B.Qk24.colM I d * Y * UpperTheory.Reformulated.B.Qk24.rowM I b

private theorem UpperTheory.Reformulated.B.Qk24.sandwich_mul {R : Type*} [Semiring R] {n k : Type*} [Fintype n] [Fintype k]
    (B C : Matrix n k R) (P Q : Matrix k n R) (X Y : Matrix k k R) :
    B * X * P * (C * Y * Q) = B * (X * (P * C * Y)) * Q := by
  simp only [Matrix.mul_assoc]

private theorem UpperTheory.Reformulated.B.Qk24.block_mul {R : Type*} [Semiring R] {n k : Type*} [Fintype n] [Fintype k]
    [DecidableEq n] (B D : Matrix n k R) (P Q : Matrix k n R) (H K : Matrix k k R)
    (h1 : P * B = H) (h2 : P * D = 0) (h3 : Q * B = 0) (h4 : Q * D = K) (X Y X' Y' : Matrix k k R) :
    (1 + B * X * P + D * Y * Q) * (1 + B * X' * P + D * Y' * Q) =
      1 + B * (X + X' + X * (H * X')) * P + D * (Y + Y' + Y * (K * Y')) * Q := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    UpperTheory.Reformulated.B.Qk24.sandwich_mul, h1, h2, h3, h4, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  abel

theorem UpperTheory.Reformulated.B.Qk24.Mk_mul :
    ∀ {I : Formalism.MainNotions.S.AutInst} {k : ℕ} (b d : Fin k → UpperTheory.Reformulated.B.Qk24.VA I) (η : TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)),
      UpperTheory.Reformulated.B.Qk24.rowM I d * UpperTheory.Reformulated.B.Qk24.colM I b =
          η • (1 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) →
        UpperTheory.Reformulated.B.Qk24.rowM I d * UpperTheory.Reformulated.B.Qk24.colM I d =
            (0 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) →
          UpperTheory.Reformulated.B.Qk24.rowM I b * UpperTheory.Reformulated.B.Qk24.colM I b =
              (0 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) →
            UpperTheory.Reformulated.B.Qk24.rowM I b * UpperTheory.Reformulated.B.Qk24.colM I d =
                (UpperTheory.Reformulated.B.Qk24.sigA I :
                            TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F) → TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))
                    η •
                  (1 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) →
              ∀ (X Y X' Y' : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))),
                UpperTheory.Reformulated.B.Qk24.Mk I b d X Y * UpperTheory.Reformulated.B.Qk24.Mk I b d X' Y' =
                  UpperTheory.Reformulated.B.Qk24.Mk I b d
                    (X + X' + X * (η • (1 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) * X'))
                    (Y + Y' +
                      Y *
                        ((UpperTheory.Reformulated.B.Qk24.sigA I :
                                      TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F) → TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))
                              η •
                            (1 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) *
                          Y')) := by
  intro I k b d η h1 h2 h3 h4 X Y X' Y'
  exact UpperTheory.Reformulated.B.Qk24.block_mul _ _ _ _ _ _ h1 h2 h3 h4 X Y X' Y'
