import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamWeightDirectSum

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open Formalism.MainNotions.SumRepresentations.At (sumRep)

namespace UpperTheory.Gal.TP.Sub

theorem denseId_holds : CpFacts → DgFacts → DenseId := by
  intro _ _ Γ _ _ l _ m m' t t' r r' a a' hr hr' ha ha' D hD hEq g
  apply Polynomial.funext
  intro x
  have key : ∀ {n : ℕ} (s : Γ →* GL (Fin n) (Qbar l)), Continuous s →
      Continuous fun g => (cp s g).eval x := by
    intro n s hs
    simp only [cp, Matrix.eval_charpoly]
    exact (continuous_const.sub (Units.continuous_val.comp hs)).matrix_det
  have keyl : ∀ {n : ℕ} (b : Fin n → Γ →* (Qbar l)ˣ), (∀ i, Continuous (b i)) →
      Continuous fun g => (lin b g).eval x := by
    intro n b hb
    simp only [lin, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    exact continuous_finset_prod _ fun i _ =>
      continuous_const.sub (Units.continuous_val.comp (hb i))
  have h := Continuous.ext_on hD ((key r hr).mul (keyl a' ha')) ((key r' hr').mul (keyl a ha))
    (fun g hg => by
      simp only [Pi.mul_apply]
      rw [← Polynomial.eval_mul, ← Polynomial.eval_mul, hEq g hg])
  have hg := congrFun h g
  simp only [Pi.mul_apply] at hg
  rw [Polynomial.eval_mul, Polynomial.eval_mul]
  exact hg

end UpperTheory.Gal.TP.Sub

end
