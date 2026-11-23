import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRs
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section
namespace GlobalTheory.CompanionTheory.WSum

variable {D : D7}

theorem trace_incA_algebraMap_mul (D : D7) (β : D.host.F) (z : AE D) :
    Algebra.trace (AF D.host.F) (AE D) (incA D (algebraMap D.host.F D.host.E β) * z) =
      algebraMap D.host.F (AF D.host.F) β * Algebra.trace (AF D.host.F) (AE D) z := by
  have h : incA D (algebraMap D.host.F D.host.E β) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) β) := by
    show (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E β) =
      (algebraMap D.host.F (AF D.host.F) β) ⊗ₜ[D.host.F] (1 : D.host.E)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [h, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem theta_half_rs {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    {α β : D.host.F} (hβ : β + β = α) (s : ℝ) (t : AE D) (ρ : D.what₂.Tau) :
    θ ρ (infPart D (incA D (algebraMap D.host.F D.host.E β) * (rs σ s * t))) =
      ((1 / 2 * s : ℝ) : ℂ) * θ ρ (infPart D (incA D (algebraMap D.host.F D.host.E α) * t)) := by
  have hi : ∀ e, θ ρ (infPart D (incA D e)) = tauE D ρ e := fun e => (hσ.inf ρ).1 e
  have hs : θ ρ (infPart D (rs σ s)) = (s : ℂ) := hσ.comp _ ρ
  have hb : tauE D ρ (algebraMap D.host.F D.host.E α) =
      tauE D ρ (algebraMap D.host.F D.host.E β) + tauE D ρ (algebraMap D.host.F D.host.E β) := by
    rw [← map_add, ← map_add, hβ]
  rw [map_mul (infPart D), map_mul (θ ρ), hi, map_mul (infPart D), map_mul (θ ρ), hs,
    map_mul (infPart D), map_mul (θ ρ), hi, hb]
  push_cast
  ring

theorem psi_halfTr_rs : ∀ (D : D7) (ψ ψ₀ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ₀ (-1) → ∀ α : D.host.F,
    (∀ x, ψ x = ψ₀ (algebraMap D.host.F (AF D.host.F) α * x)) → ∀ (θ : InfFam D)
    (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (t : AE D) (s : ℝ),
    ψ (halfTr (rs σ s * t)) = Complex.exp (2 * Real.pi * Complex.I * ((s * lam θ α t : ℝ) : ℂ)) := by
  intro D ψ ψ₀ h₀ α hψ θ σ hσ t s
  obtain ⟨β, hβ', hβ⟩ : ∃ β : D.host.F, β = α * (1 / 2) ∧ β + β = α := ⟨_, rfl, by ring⟩
  set z' : AE D := incA D (algebraMap D.host.F D.host.E β) * (rs σ s * t) with hz'
  have hR : algebraMap D.host.F (AF D.host.F) α * halfTr (rs σ s * t) =
      Algebra.trace (AF D.host.F) (AE D) z' := by
    rw [hz', trace_incA_algebraMap_mul, hβ', map_mul, mul_assoc]
    rfl
  have hfin : finPart D z' = 0 := by
    have h0 : finPart D (rs σ s) = 0 := hσ.fin _
    rw [hz', map_mul (finPart D), map_mul (finPart D) (rs σ s), h0, zero_mul, mul_zero]
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  set R := Algebra.trace (AF D.host.F) (AE D) z' with hRdef
  have h1 : ψ₀ R = psiInf D.host.F ψ₀ (fstA D.host.F R) := by
    unfold psiInf
    rw [← hT]
  have h2 := h₀.2.2 θ hσ.inf (fstA D.host.F R)
  have h3 : ∀ ρ, θ ρ (fstA D.host.F R ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((s * (θ ρ (infPart D (incA D (algebraMap D.host.F D.host.E α) * t))).re : ℝ) : ℂ) := by
    intro ρ
    rw [hRdef, GlobalTheory.PhaseReal.theta_trace θ hσ.inf ρ z', hz', theta_half_rs hσ hβ, Complex.re_ofReal_mul]
    congr 1
    ring
  rw [hψ, hR, h1, h2]
  congr 1
  simp only [h3]
  rw [← Complex.ofReal_sum, ← Finset.mul_sum]
  unfold lam
  push_cast
  ring

end GlobalTheory.CompanionTheory.WSum
