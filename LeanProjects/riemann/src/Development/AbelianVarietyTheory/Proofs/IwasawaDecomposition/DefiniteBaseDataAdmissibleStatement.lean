import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteBaseDataAdmissible
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
import Formalism.LocalToGlobal.Columns.BaseLemmas
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBaseData_admissible : ∀ (B : Base) (X : PreX B.toPre) (Ch : Chars B.fields (B.primes X) B.R.m), Ch.Ok → Ch.FromHecke B.wts B.embLL → (B.dat X Ch).Ok := by
  first | exact @GlobalTheory.Mem.DatLaws.dat_ok | exact GlobalTheory.Mem.DatLaws.dat_ok | (intros; apply GlobalTheory.Mem.DatLaws.dat_ok <;> assumption)
