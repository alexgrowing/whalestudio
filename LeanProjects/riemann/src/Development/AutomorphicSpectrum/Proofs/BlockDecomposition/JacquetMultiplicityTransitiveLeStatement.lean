import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityTransitiveLe
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_transitive_le : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {g N : ℕ} (y : Fin g → IrrGL k) (hy : ∑ b, (y b).1 = N) (Wb : Fin g → List (IrrGL k)) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → (∀ b, ∑ a, ((Wb b).get a).1 = (y b).1) → jm y hy π * ∏ b, jmL (Wb b) (y b).rep ≤ jmL (List.ofFn Wb).flatten π := by
  first | exact @GlobalTheory.CompanionTheory.CsStages.jm_mul_prod_jmL_le | exact GlobalTheory.CompanionTheory.CsStages.jm_mul_prod_jmL_le | (intros; apply GlobalTheory.CompanionTheory.CsStages.jm_mul_prod_jmL_le <;> assumption)
