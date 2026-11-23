import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareCommutationIntegralIdentity
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_commutation_integral_identity : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
    GlobalTheory.SquareComm.IsTriple W W₁ X α β →
    ∀ (ν : MeasureTheory.Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : MeasureTheory.Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)),
    GlobalTheory.SquareComm.IsHaarFD W ν 𝓕 → GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ GlobalTheory.SquareComm.algF ψ θ true A B, ∀ Φ' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B,
      (∀ h, MeasureTheory.IntegrableOn (fun g => thetaKO ωB g h Φ') 𝓕₁ ν₁) → p Φ = p' Φ' →
      GlobalTheory.SquareComm.thetaInt ωA ν 𝓕 Φ = c • GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ' := by
  first | exact @GlobalTheory.ThetaAgreeConv.thetaIntegralsAgree_of_integrable | exact GlobalTheory.ThetaAgreeConv.thetaIntegralsAgree_of_integrable | (intros; apply GlobalTheory.ThetaAgreeConv.thetaIntegralsAgree_of_integrable <;> assumption)
