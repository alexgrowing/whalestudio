import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialFourierSumInverseOfLatticeDepth
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialFourierSum_inverse_of_latticeDepth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A : Type) [Fintype A] [DecidableEq A] (C : Type) [Fintype C] [DecidableEq C] (ψ : AddChar k Circle) (ϖ : kˣ) (n : ℕ) (P : Finset C), IsUnif ϖ → HasConductor ψ 1 →
    ∀ Ξ : Matrix A C k → ℂ, HasDepth ϖ n (blockLat ϖ n P) Ξ → fourierSum ψ ϖ n P (invFourierSum ψ ϖ n P Ξ) = Ξ := by
  first | exact @GlobalTheory.FlipMatch.FourierInv.fourierSum_invFourierSum | exact GlobalTheory.FlipMatch.FourierInv.fourierSum_invFourierSum | (intros; apply GlobalTheory.FlipMatch.FourierInv.fourierSum_invFourierSum <;> assumption)
