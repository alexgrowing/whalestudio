import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivativeFockVectorsUniformOperator
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RouteDatumMemAlgebraicVectorsGridFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergOpArchimedeanSumRealPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSecondPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationPreservesFockVectorsTwoFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialOperatorHeisenbergDerivative

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDerivative_fockVectors_uniform_operator : ∀ {D : D7} {V W : HSp D} (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ}, IsStdChar D ψ (-1) → IsInfFam θ → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ), ∃ Δ : PolF D W.rank V.rank →ₗ[ℂ] PolF D W.rank V.rank, ∀ f, GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ P, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (GlobalTheory.ChainFr.ptF ψ θ A B f P) = GlobalTheory.ChainFr.ptF ψ θ A B f (Δ P) := by
  first | exact @GlobalTheory.FockDerUnif.dRho_ptF_uniform | exact GlobalTheory.FockDerUnif.dRho_ptF_uniform | (intros; apply GlobalTheory.FockDerUnif.dRho_ptF_uniform <;> assumption)
