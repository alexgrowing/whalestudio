import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiUnipotentTrivialOnLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialSuperdiagonalOffExceptionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdditiveCharacterSuperdiagTrivialStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.UniBF

private theorem psiE_add_mul {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (a b : AE D) :
    psiE ψ (a + b) = psiE ψ a * psiE ψ b := by
  simp only [psiE, map_add, AddChar.map_add_eq_mul]

private theorem psiE_zero_one {D : D7} (ψ : AddChar (AF D.host.F) ℂ) : psiE ψ (0 : AE D) = 1 := by
  simp only [psiE, map_zero, AddChar.map_zero_eq_one]

theorem psiUni_pcBF : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u : UX D ρ,
    MxAt (fun _ => True) (u.1.1 - 1) → xZero (F.dJ ρ h) ⬝ u.1.1 - xZero (F.dJ ρ h) ∈ (pcBF W F ρ h).A₁ →
    psiUni W.ψ u.1 = 1 := by
  intro D hq T L μ0 hL sc G W Mv hM F hF ρ h u hu hx
  have hA := GlobalTheory.T.genericCharacter_trivial_superdiagonal_off_exceptional D hq T L μ0 hL sc G W Mv hM F hF ρ h
  have hB := GlobalTheory.T.additive_character_superdiag_trivial D hq T L μ0 hL sc G W Mv hM F hF ρ h
  set N : Mx D ρ ρ := u.1.1 - 1 with hNdef
  have hx' : (F.dB ρ h).extX _ ((F.dJ ρ h).jX ⬝ N) ∈ latRow G (2 * ρ + 1) := by
    have e : xZero (F.dJ ρ h) ⬝ u.1.1 - xZero (F.dJ ρ h) = (F.dJ ρ h).jX ⬝ N := by
      rw [hNdef, Matrix.mul_sub, Matrix.mul_one]; rfl
    rw [← e]; exact hx
  have hN : (F.dJ ρ h).pX ⬝ ((F.dB ρ h).extX _ ((F.dJ ρ h).jX ⬝ N) ⬝ (F.dB ρ h).jX) = N := by
    rw [HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one, ← Matrix.mul_assoc, HypDec.pX_jX,
      Matrix.one_mul]
  have key : ∀ i j : Fin ρ, j.1 = i.1 + 1 → psiE W.ψ (u.1.1 i j) = 1 := fun i j hij => by
    have hne : i ≠ j := fun e => by rw [e] at hij; omega
    have e1 : u.1.1 i j = N i j := by rw [hNdef, Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]
    rw [e1]
    refine GlobalTheory.FinPl.PsiUnit.psiE_eq_one_of_local W.ψ W.ψ_std.1.1 (hu i j) fun v _ => ?_
    have ho := GlobalTheory.FinPlLoc.idem_mem_intAt (D := D) (· = v)
    by_cases hv : v ∈ G.pl.S0
    · have := hB _ hx' i j hij v hv _ ho
      rwa [hN] at this
    · have := hA _ hx' i j hij v hv _ ho
      rwa [hN] at this
  unfold psiUni upSum
  refine Finset.sum_induction _ (fun x => psiE W.ψ x = 1) (fun a b ha hb => by rw [psiE_add_mul, ha, hb, one_mul])
    (psiE_zero_one W.ψ) fun i _ => ?_
  refine Finset.sum_induction _ (fun x => psiE W.ψ x = 1) (fun a b ha hb => by rw [psiE_add_mul, ha, hb, one_mul])
    (psiE_zero_one W.ψ) fun j _ => ?_
  split_ifs with hij
  · exact key i j hij
  · exact psiE_zero_one W.ψ

example : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u : UX D ρ, MxAt (fun _ => True) (u.1.1 - 1) →
    xZero (F.dJ ρ h) ⬝ u.1.1 - xZero (F.dJ ρ h) ∈ (pcBF W F ρ h).A₁ → psiUni W.ψ u.1 = 1 := psiUni_pcBF

end GlobalTheory.AscFin.UniBF

end
