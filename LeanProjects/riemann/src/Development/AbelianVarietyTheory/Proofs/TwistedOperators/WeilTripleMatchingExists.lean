import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationsForTripleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameBaseExistsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameCompatibilityStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.TripleRead

theorem exists_isMatch : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
      ∃ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' := by
  intro hH hP _ hLM D ψ θ hψ hθ W W₁ X A A₁ B α β hT
  obtain ⟨ωA, ωB, hA, hB⟩ := GlobalTheory.T.weil_representations_for_triple hP D ψ hψ W W₁ X α β hT
  obtain ⟨e, Bs, Γ, Xc, om, om', h, hTr, htA, htB⟩ := GlobalTheory.T.triple_frame_base_exists hP D ψ hψ W W₁ X A A₁ B α β hT ωA ωB hA hB
  obtain ⟨R, Rf, hM⟩ := hLM D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTr
  obtain ⟨Pi, rf, rl, p, p', hm⟩ :=
    GlobalTheory.T.triple_frame_compatibility hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h htA htB R Rf hM
  exact ⟨ωA, ωB, Pi, rf, rl, p, p', hm⟩

end GlobalTheory.TripleRead

end
