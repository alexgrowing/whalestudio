import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorEmbeddingsExist
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisExtra
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.position_embeddings_exist : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (a b : ℕ) {S : Set (Pl E)} (hS : IsSection S),
    ∃ e : ∀ i : Slot S, (GLw a i.pl × GLw b i.pl) →* Hf E a b,
      (∀ i, Continuous (e i)) ∧ (∀ (i : Slot S) m, i.cp a b (e i m) = m) ∧ (∀ (i j : Slot S) m, i ≠ j → j.cp a b (e i m) = 1) ∧
      (∀ (w : {w // w ∈ S}) (m : GLw a w.1 × GLw b w.1),
        finH (e (.inl w) m) = (embW a w.1 m.1, embW b w.1 m.2)) ∧
      ∀ (w : {w // w ∈ S ∧ IsSplitAt w}) (m : GLw a w.1 × GLw b w.1),
        finH (e (.inr w) m) = (embT a w.1 m.1, embT b w.1 m.2) := by
  first | exact @GlobalTheory.CompanionTheory.FinActS.exists_factorEmb | exact GlobalTheory.CompanionTheory.FinActS.exists_factorEmb | (intros; apply GlobalTheory.CompanionTheory.FinActS.exists_factorEmb <;> assumption)
