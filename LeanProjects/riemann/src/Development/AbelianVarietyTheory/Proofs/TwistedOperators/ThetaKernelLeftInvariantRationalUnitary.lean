import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedThetaIntegralValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

noncomputable section

namespace GlobalTheory.SquareComm.ThetaLeft

theorem isThetaFunO_of_mem_algF {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) {M X : HSp D} (A : Fr M) (B : Fr X) {Φ : WO M X → ℂ} (hΦ : Φ ∈ algF ψ θ false A B) :
    IsThetaFunO ψ M X Φ := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, P, hf, rfl⟩ := hx
    exact GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ _ _ _ _ hf.1 P
  | zero => exact GlobalTheory.OrientedHeis.theta_zero
  | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
  | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (M X : HSp D) (A : Fr M) (B : Fr X)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X), IsWeil ψ false M X χ χ' ω → ∀ Φ ∈ algF ψ θ false A B, ∀ γ ∈ GQ M,
    ∀ (g : GA D M) (h : GA D X), thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := by
  intro D ψ θ hθ M X A B χ χ' ω hω Φ hΦ γ hγ g h
  have hω' : IsWeilDatumO ψ M X χ χ' ω := hω
  have hth : IsThetaFunO ψ M X Φ := isThetaFunO_of_mem_algF hω'.std hθ A B hΦ
  unfold thetaKO
  have e : (γ * g, h) = (γ, (1 : GA D X)) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hω'.om_aut _ hγ _ (Subgroup.one_mem _) _ (hω'.om_pres _ _ hth)

end GlobalTheory.SquareComm.ThetaLeft
