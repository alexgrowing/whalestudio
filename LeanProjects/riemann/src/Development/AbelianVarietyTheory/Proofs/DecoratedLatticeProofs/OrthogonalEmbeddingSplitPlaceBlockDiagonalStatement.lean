import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthogonalEmbeddingSplitPlaceBlockDiagonal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
open GlobalTheory.RootEx (embX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalEmbedding_splitPlace_blockDiagonal : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (σ : ℕ) (B : BesLev D σ) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)), IsSumFrame B.o B.ζ β β₀ → ∀ g : GL n k, B.o.emb (β.gl g, 1) = β₀.gl (embX 1 g) := by
  first | exact @GlobalTheory.FinPl.emb_gl_sumFrame | exact GlobalTheory.FinPl.emb_gl_sumFrame | (intros; apply GlobalTheory.FinPl.emb_gl_sumFrame <;> assumption)
