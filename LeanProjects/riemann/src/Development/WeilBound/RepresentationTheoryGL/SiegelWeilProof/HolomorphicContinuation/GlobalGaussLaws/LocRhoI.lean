import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInstSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoB
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoE
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoF
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoH
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorSchrodingerModelIsKFiniteStatement

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

theorem phiS_val {m : ℕ} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ} {c : ℝ} {Ψ : Mx D m n → ℂ}
    {P : PX m n} (h : tens θ τ fr (fP c P) Ψ ∈ schwartzA θ m n) : (phiS θ τ fr c Ψ P).1 = tens θ τ fr (fP c P) Ψ := by
  delta PositivityTheory.Rg.Sw.Glob.phiS
  rw [dif_pos h]

theorem tens_add_smul {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (a : ℂ)
    (f g : (Fin m → Fin n → ℂ) → ℂ) (Ψ : Mx D m n → ℂ) :
    tens θ τ fr (a • f + g) Ψ = a • tens θ τ fr f Ψ + tens θ τ fr g Ψ := by
  funext x
  delta PositivityTheory.Rg.Sw.Glob.tens
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change (a * f (fr⁻¹ * compAt θ τ x) + g (fr⁻¹ * compAt θ τ x)) * Ψ x = _
  ring

theorem tensor_gaussian_vacuum_injective {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (l : D.what₂.Tau → ℝ) {f g : (Fin V.rank → Fin n → ℂ) → ℂ}
    (h : tens θ τ fr f (psi0 θ V n l s τ) = tens θ τ fr g (psi0 θ V n l s τ)) : f = g := by
  have hdet : IsUnit fr.det := hfr.1
  suffices hU : ∀ U : Matrix (Fin V.rank) (Fin n) ℂ, f U = g U from funext hU
  intro U
  have hx := congrFun h (xL θ τ (fr * U))
  have hc : compAt θ τ (xL θ τ (fr * U)) = fr * U := by
    have h1 := congrFun (compAt_xL hθ τ (fr * U)) τ
    simpa [dirAt_self] using h1
  have hp : psi0 θ V n l s τ (xL θ τ (fr * U)) = 1 := by
    show gAway V l s τ (fun τ' => compAt θ τ' (xL θ τ (fr * U))) *
      g0 D V.rank n (fun i j => finPart D (xL θ τ (fr * U) i j)) = 1
    rw [compAt_xL hθ, gAway_dirAt, finPart_xL hθ, gaussian_at_zero_eq_one, one_mul]
  have hinv : fr⁻¹ * (fr * U) = U := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul fr hdet, Matrix.one_mul]
  change f (fr⁻¹ * compAt θ τ (xL θ τ (fr * U))) * psi0 θ V n l s τ (xL θ τ (fr * U)) =
    g (fr⁻¹ * compAt θ τ (xL θ τ (fr * U))) * psi0 θ V n l s τ (xL θ τ (fr * U)) at hx
  rw [hc, hp, hinv, mul_one, mul_one] at hx
  exact hx

end PositivityTheory.Rg.Sw.Glob.RhoH
