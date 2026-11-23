import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondActionOnHermitianChartClasses
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamond_action_on_hermitianChartClasses : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → (∀ P c, S.cl c.1 (A.diaPt P 1 c) = c) ∧ (∀ P a b c, S.cl c.1 (A.diaPt P (a * b) c) = S.cl c.1 (A.diaPt P a (S.cl c.1 (A.diaPt P b c)))) ∧ ∀ P a c, Nat.card (S.Stab (S.cl c.1 (A.diaPt P a c))) = Nat.card (S.Stab c) := by
  first | exact @GlobalTheory.Mem.Col2.diamond_action_on_classes | exact GlobalTheory.Mem.Col2.diamond_action_on_classes | (intros; apply GlobalTheory.Mem.Col2.diamond_action_on_classes <;> assumption)
