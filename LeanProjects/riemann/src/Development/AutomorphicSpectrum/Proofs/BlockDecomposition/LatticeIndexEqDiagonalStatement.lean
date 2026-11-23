import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIndexEqDiagonal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_index_eq_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (i j : ℕ), i ≤ a → j ≤ b → ∀ m : GLw a w × GLw b w, Tj ℂ a (Ov E w) ϖ i m.1 ≠ 0 → Tj ℂ b (Ov E w) ϖ j m.2 ≠ 0 → (intSub a b w).relIndex (latM ϖ m) = (intSub a b w).relIndex (latD ϖ a b i j) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.Tr.latM_relIndex | exact GlobalTheory.CompanionTheory.CtS.Tr.latM_relIndex | (intros; apply GlobalTheory.CompanionTheory.CtS.Tr.latM_relIndex <;> assumption)
