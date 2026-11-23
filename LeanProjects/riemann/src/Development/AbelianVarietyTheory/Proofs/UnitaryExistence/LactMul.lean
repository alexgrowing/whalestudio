import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ContinuousIffCrdA
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InvariantProbabilityLatticeQuotientUniqueStatement

namespace GlobalTheory.LeftActionMul

open ReciprocityTheory.ChartRestriction.G.FD

theorem lact_mul {E : Type} [Field E] {r : ℕ} {Ψ : Finset (E →+* ℂ)} (δ δ' : GL (Fin r) E)
    (y : Frame Ψ r) : lact (δ * δ') y = lact δ (lact δ' y) := by
  funext τ
  have h1 : ((δ * δ' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) =
      (δ : Matrix (Fin r) (Fin r) E) * (δ' : Matrix (Fin r) (Fin r) E) := Units.val_mul δ δ'
  have h2 : ((δ : Matrix (Fin r) (Fin r) E) * (δ' : Matrix (Fin r) (Fin r) E)).map τ.1 =
      (δ : Matrix (Fin r) (Fin r) E).map τ.1 * (δ' : Matrix (Fin r) (Fin r) E).map τ.1 :=
    Matrix.map_mul
  show ((δ * δ' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ =
    (δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (lact δ' y) τ
  rw [h1, h2, Matrix.mul_assoc]
  rfl

theorem main : ∀ {E : Type} [inst : Field E] {r : ℕ} {Ψ : Finset (E →+* ℂ)} (δ δ' : GL (Fin r) E)
    (y : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r),
    ReciprocityTheory.ChartRestriction.G.FD.lact (δ * δ') y = ReciprocityTheory.ChartRestriction.G.FD.lact δ (ReciprocityTheory.ChartRestriction.G.FD.lact δ' y) :=
  fun δ δ' y => lact_mul δ δ' y

end GlobalTheory.LeftActionMul
