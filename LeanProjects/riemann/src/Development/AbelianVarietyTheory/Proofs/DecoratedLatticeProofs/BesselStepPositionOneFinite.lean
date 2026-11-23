import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearIsQuotIntTIntStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsQuotientInvariantIntegralExchangeToPositionOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.PosOne.quotInt_one_comb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (e : GL (n' ⊕ Fin (c + 1)) k →₀ ℂ) (_ : SrcComb ψ ν P ρ' Φ e) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ P σ B) (F : A) (z : GL (n' ⊕ Fin (c + 1)) k → ℂ), (∀ g ∈ e.support, IsQuotInt ν μX μG P (tInt ψ ν μ P σ B F (om μ g 1 Φ.1)) (z g)) → IsQuotInt ν μX μG 1 (tIntOne ψ ν μ P σ B F Φ.1) (comb e z) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c P hP hPc ψ hψ hψ1 ν hν μ hμ μX _ μG _ ρ' hρ' Φ e he A _ _ σ hσ B hB F z hz
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨Rr, hRr, hRrN⟩ := GlobalTheory.T.exists_linear_isQuotInt_tInt_alt k n n' c P hP hPc ψ hψ hψ1 ν μ hμ μX μG A σ hσ B hB F ρ' hρ'
  have hone := GlobalTheory.T.isQuotientInvariantIntegral_exchange_toPositionOne k n n' c P hP hPc ψ hψ hψ1 ν hν μ hμ μX μG A σ hσ B hB F ρ' hρ' Rr hRr Φ
  have hcomb : toOne ν ρ' P Rr Φ = comb e fun g => Rr (ρ' g Φ) := he Rr hRrN
  have heq : comb e z = comb e fun g => Rr (ρ' g Φ) := by
    unfold comb
    refine Finsupp.sum_congr fun g hg => ?_
    congr 1
    have h1 := hRr (ρ' g Φ)
    rw [hρ' g Φ] at h1
    exact ((GlobalTheory.QuotInt.quotInt_unique_exists k n c P hP hPc ν μX μG _).1 _ _ (hz g hg) h1)
  rw [heq, ← hcomb]
  exact hone
