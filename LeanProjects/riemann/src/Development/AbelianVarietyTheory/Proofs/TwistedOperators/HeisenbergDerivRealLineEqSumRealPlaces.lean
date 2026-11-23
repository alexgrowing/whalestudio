import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDirectionalDerivFormulaAndSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGaussEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDarbouxOrientedPairTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchLineApply

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer

namespace GlobalTheory.PlaceSum
open GlobalTheory.OrientedHeis GlobalTheory.FockCompare

theorem hD_finset_sum {G R : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (f : G → ℂ) (hf : Sm ι f) {α : Type} (s : Finset α)
    (u : α → R) : hD ι π om (∑ a ∈ s, u a) f = ∑ a ∈ s, hD ι π om (u a) f := by
  funext w
  rw [Finset.sum_apply]
  simp only [hD_eq_fderiv ι π om f hf, map_sum, ContinuousLinearMap.sum_apply]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]

theorem deriv_heisO_eq_sum_dRho : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ L : ℝ →+ WO S T, Continuous L →
      (∀ t, (L t).map (finPart D) = 0) →
      (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) f w) 0) =
        ∑ τ, dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f := by
  intro D ψ hψ θ hθ S T f hf L hLc hLf
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e1 : (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) f w) 0) =
      hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (L 1)) f :=
    dLine_eq_hD h hψ (L := L) ⟨hLc, hLf⟩ f
  have e2 : ∀ τ, dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f =
      hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (lineAt θ τ (compAt θ τ (L 1)) 1)) f := by
    intro τ
    have hl := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (compAt θ τ (L 1))
    rw [dRho_eq_dLine]
    exact dLine_eq_hD h hψ ⟨hl.1, hl.2.1⟩ f
  have e3 : piW θ T S (L 1) = ∑ τ, piW θ T S (lineAt θ τ (compAt θ τ (L 1)) 1) := by
    funext τ' i j
    simp only [Finset.sum_apply]
    have hc : ∀ τ, piW θ T S (lineAt θ τ (compAt θ τ (L 1)) 1) τ' i j =
        compAt θ τ' (lineAt θ τ (compAt θ τ (L 1)) 1) i j := fun τ => rfl
    simp only [hc]
    rw [Finset.sum_eq_single τ']
    · rw [(GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ' (compAt θ τ' (L 1))).2.2 1 τ', if_pos rfl, Complex.ofReal_one,
        one_smul]
      rfl
    · intro b _ hb
      rw [(GlobalTheory.WeilVacMove.isLineAt_lineAt hθ b (compAt θ b (L 1))).2.2 1 τ', if_neg (Ne.symm hb)]
      rfl
    · intro hn; exact absurd (Finset.mem_univ τ') hn
  rw [e1, e3, hD_finset_sum _ _ _ f (theta_sm h hf)]
  exact Finset.sum_congr rfl fun τ _ => (e2 τ).symm

end GlobalTheory.PlaceSum
