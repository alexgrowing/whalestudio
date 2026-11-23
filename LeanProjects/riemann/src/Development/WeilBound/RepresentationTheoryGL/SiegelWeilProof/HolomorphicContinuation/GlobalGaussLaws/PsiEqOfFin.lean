import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTraceEqAddStar
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousPsiT

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.StdUnn
open Formalism.IndefR.Eqv (psiT psiT_sigR thetaC eq_thetaC)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTP

variable {D : D7}

set_option synthInstance.maxHeartbeats 400000 in

theorem incl_trA (z : AE D) : algebraMap (AF D.host.F) (AE D) (trA z) = z + cA D z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [trA]
  | tmul a e =>
    simp only [trA]
    rw [GlobalTheory.SplitAdeleTrace.trace_baseChange_tmul (AF D.host.F) a e]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have h : (Algebra.trace D.host.F D.host.E e : D.host.E) = e + star e := GlobalTheory.TraceAddStar.trace_eq_add_star e
    calc (a * algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e)) ⊗ₜ[D.host.F] (1 : D.host.E)
        = a ⊗ₜ[D.host.F] ((Algebra.trace D.host.F D.host.E e : D.host.F) : D.host.E) := by
          rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]; rfl
      _ = a ⊗ₜ[D.host.F] e + cA D (a ⊗ₜ[D.host.F] e) := by
          rw [h, TensorProduct.tmul_add]; rfl
  | add x y hx hy =>
    simp only [trA, map_add] at hx hy ⊢
    rw [hx, hy]; abel

set_option synthInstance.maxHeartbeats 400000 in

theorem psi_eq_of_fin {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {l : D.what₂.Tau → ℝ}
    (hl : HasRealPar ψ θ l) (a : AF D.host.F) (ha : finPart D (algebraMap (AF D.host.F) (AE D) a) = 0) :
    ψ a = Complex.exp (2 * Real.pi * Complex.I * ∑ τ, (l τ : ℂ) * psiT D τ (algebraMap (AF D.host.F) (AE D) a)) := by
  have hsnd : sndA D.host.F a = 0 := by
    apply Algebra.TensorProduct.includeLeft_injective (S := Af D.host.F) (algebraMap D.host.F D.host.E).injective
    rw [map_zero]
    exact ha
  have ha' : a = pairA D.host.F (fstA D.host.F a) 0 := Prod.ext rfl hsnd
  have h1 : ψ a = psiInf D.host.F ψ (fstA D.host.F a) := by
    conv_lhs => rw [ha']
    rfl
  rw [h1, hl, eq_thetaC D hθ]
  rfl

set_option synthInstance.maxHeartbeats 400000 in

theorem psi_trA_tau {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {l : D.what₂.Tau → ℝ}
    (hl : HasRealPar ψ θ l) (τ : D.what₂.Tau) (z : AE D) (hz : ∀ τ', τ' ≠ τ → psiT D τ' z = 0)
    (hzf : finPart D z = 0) :
    ψ (trA z) = Complex.exp (Complex.I * ((4 * Real.pi * l τ : ℝ) : ℂ) * ((psiT D τ z).re : ℂ)) := by
  have hfin : finPart D (algebraMap (AF D.host.F) (AE D) (trA z)) = 0 := by
    rw [incl_trA, RingHom.map_add, hzf, cA, Formalism.IndefR.Eqv.finPart_sigR, hzf, RingHom.map_zero, add_zero]
  rw [psi_eq_of_fin hθ hl _ hfin, incl_trA]
  have hs : ∑ τ', (l τ' : ℂ) * psiT D τ' (z + cA D z) = (l τ : ℂ) * (2 * ((psiT D τ z).re : ℂ)) := by
    rw [Finset.sum_eq_single τ]
    · rw [RingHom.map_add, cA, psiT_sigR, Complex.add_conj]; push_cast; ring
    · intro τ' _ hne
      rw [RingHom.map_add, cA, psiT_sigR, hz τ' hne, map_zero, add_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ τ) h
  rw [hs]
  congr 1
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.FTP
