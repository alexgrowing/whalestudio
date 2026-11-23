import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyAt0Smul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackConstantSqEqDet

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.VacuumUnique

theorem vacuum_unique : ∀ {D : D7}, Inp D → ∀ {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ}, Crv D cc δ → ∀ {N N' : ℕ} {e₁ e₂ : VC D N N' → ℂ}, oddE0 D cc δ t0 N N' e₁ → oddE0 D cc δ t0 N N' e₂ → e₁ ≠ 0 → ∃ κ : ℂ, ‖κ‖ = 1 ∧ e₂ = κ • e₁ := by
  intro D _ cc δ t0 hC N N' e₁ e₂ h₁ h₂ hne
  have hG1 := (GlobalTheory.InducedType.induced_type D).1
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') :=
    GlobalTheory.NormSum.VacMove.klat _ (GlobalTheory.NormSum.VacMove.moves_one D N) (GlobalTheory.NormSum.VacMove.moves_one D N')
  obtain ⟨hline, -⟩ := GlobalTheory.ThetaLine.theta_line D hG1 cc δ hC N N' _ k0
  obtain ⟨c, hc⟩ := hline e₂ h₂.1 e₁ h₁.1 hne
  refine ⟨c, ?_, hc⟩
  have hn := GlobalTheory.UnitaryTheta.normSq_ne_zero D cc δ hC k0 h₁.1 hne
  have e := h₂.2.2.1.trans h₁.2.2.1.symm
  rw [hc, GlobalTheory.UnitaryTheta.normSq_smul] at e
  have h1 : ‖c‖ ^ 2 = 1 := by
    have := mul_right_cancel₀ hn (e.trans (one_mul _).symm)
    exact this
  have h0 : 0 ≤ ‖c‖ := norm_nonneg c
  nlinarith [sq_nonneg (‖c‖ - 1), sq_nonneg (‖c‖ + 1)]

end GlobalTheory.VacuumUnique
