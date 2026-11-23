import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulMemComplId
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartTraceCharacterIdempotentInverseDiffere
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF

noncomputable section

namespace GlobalTheory.XCharBF

variable {D : D7}

theorem conj_mem_AA_mul_AAbar {a : D.host.E} (ha : a ∈ D.host.AA * D.host.AAbar) :
    D.host.conj a ∈ D.host.AA * D.host.AAbar := by
  refine FractionalIdeal.mul_induction_on (C := fun a => D.host.conj a ∈ D.host.AA * D.host.AAbar) ha ?_ ?_
  · intro x hx y hy
    rw [map_mul, mul_comm (D.host.conj x)]
    exact FractionalIdeal.mul_mem_mul (Formalism.L2.Pj.conj_mem_AA D hy) (Formalism.L2.Pj.conj_mem_AAbar D hx)
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem (p := ((D.host.AA * D.host.AAbar : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E)) hx hy

theorem hostDifferentGenerator_mul_mem_inverseDifferent {a : D.host.E} (ha : a ∈ D.host.AA * D.host.AAbar) :
    D.host.xi0 * a ∈ GlobalTheory.IdeleAA.Dual D := by
  change _ ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
  rw [← Formalism.L2.Pj.dual_eq Formalism.IndefR.Fin.factPrincipalDatum D]
  have h := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0) ha
  rwa [← mul_assoc] at h

theorem psiE_add' (ψ : AddChar (AF D.host.F) ℂ) (x y : AE D) : psiE ψ (x + y) = psiE ψ x * psiE ψ y := by
  unfold psiE
  rw [map_add, AddChar.map_add_eq_mul]

theorem psiE_zero' (ψ : AddChar (AF D.host.F) ℂ) : psiE ψ (0 : AE D) = 1 := by
  unfold psiE
  rw [map_zero, AddChar.map_zero_eq_one]

theorem cA_tmul' (p : AF D.host.F) (e : D.host.E) :
    cA D (p ⊗ₜ[D.host.F] e) = p ⊗ₜ[D.host.F] D.host.conj e := by
  rw [GlobalTheory.IdeleAA.tmul_eq, map_mul, GlobalTheory.SelfDualAt.cA_alg, GlobalTheory.IdeleAA.cA_incA, ← GlobalTheory.IdeleAA.tmul_eq]

theorem adelicTraceChar_differentGen_conj_integral_tmul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {α : Af D.host.F}
    (hα : α ∈ intAf D.host.F) {a : D.host.E} (ha : a ∈ D.host.AA * D.host.AAbar) :
    psiE ψ (incA D D.host.xi0 * cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] a)) = 1 := by
  have e : incA D D.host.xi0 * cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] a) =
      pairA D.host.F 0 α ⊗ₜ[D.host.F] (D.host.xi0 * D.host.conj a) := by
    rw [cA_tmul', GlobalTheory.IdeleAA.tmul_eq, GlobalTheory.IdeleAA.tmul_eq, map_mul]
    ring
  rw [e, GlobalTheory.FinPl.Conductor.psiE_eq_chi ψ (by exact TensorProduct.zero_tmul _ _)]
  exact GlobalTheory.IdeleAA.chi_tmul_dual hψ hα (hostDifferentGenerator_mul_mem_inverseDifferent (conj_mem_AA_mul_AAbar ha))

theorem adelicTraceChar_differentGen_conj_idealCompletion : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ}, IsStdChar D ψ (-1) →
    ∀ s ∈ complId (D.host.AA * D.host.AAbar), psiE ψ (incA D D.host.xi0 * cA D s) = 1 := by
  intro D ψ hψ s hs
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    obtain ⟨α, hα, a, ha, rfl⟩ := hs
    exact adelicTraceChar_differentGen_conj_integral_tmul hψ hα ha
  | zero => rw [map_zero, mul_zero]; exact psiE_zero' ψ
  | add x y _ _ hx hy => rw [map_add, mul_add, psiE_add', hx, hy, one_mul]
  | neg x _ hx =>
    have h := psiE_add' ψ (incA D D.host.xi0 * cA D x) (incA D D.host.xi0 * cA D (-x))
    rw [← mul_add, ← map_add, add_neg_cancel, map_zero, mul_zero, psiE_zero', hx, one_mul] at h
    exact h.symm

end GlobalTheory.XCharBF

end
