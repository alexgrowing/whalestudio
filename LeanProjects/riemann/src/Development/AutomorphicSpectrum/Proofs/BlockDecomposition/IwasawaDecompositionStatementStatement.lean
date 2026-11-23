import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_statement : GlobalTheory.CompanionTheory.Jp.JpIw := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Iw.jpIw | exact GlobalTheory.CompanionTheory.Jp.Iw.jpIw | (intros; apply GlobalTheory.CompanionTheory.Jp.Iw.jpIw <;> assumption)
