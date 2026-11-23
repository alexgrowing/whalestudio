import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsOfOkAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tDat_laws_of_ok : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → A.Laws T := by
  first | exact @GlobalTheory.Mem.Col2.TDat.laws_of_ok | exact GlobalTheory.Mem.Col2.TDat.laws_of_ok | (intros; apply GlobalTheory.Mem.Col2.TDat.laws_of_ok <;> assumption)
