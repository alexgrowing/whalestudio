import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAdjYZeroMemLatOIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentPowCompletionTrivialAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JZeroMulMemLatticeIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulInvIff
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TmulOneMemIntAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.StairIdealAt

theorem completion_eq_of_modul_unit : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (ρ : ℕ) (v : GlobalTheory.FinPl.Pl D), 0 < ρ → GlobalTheory.SeeSaw.idV ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) v = GlobalTheory.SeeSaw.idV 1 v → (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ - 1 + 1))⁻¹ * (P.stA sc ^ (2 * ρ - (ρ - 1)) * (P.stAbar sc ^ (ρ - 1 + 1))⁻¹) ≠ 0) ∧ (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ + 1))⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ (ρ + 1))⁻¹) ≠ 0) ∧ ∀ s, s ∈ GlobalTheory.SeeSaw.idV ((D.host.AAbar : GlobalTheory.SeeSaw.FI D) * (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ - 1 + 1))⁻¹ * (P.stA sc ^ (2 * ρ - (ρ - 1)) * (P.stAbar sc ^ (ρ - 1 + 1))⁻¹))⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ D.host.xi0⁻¹ * (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ + 1))⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ (ρ + 1))⁻¹))⁻¹) v := by
  intro D T L P sc ρ v hρ hM
  have hx : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hAb : (D.host.AAbar : GlobalTheory.SeeSaw.FI D) ≠ 0 := GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D
  have hMo : ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact P.modul_ne_bot sc
  have hS : P.stA sc ≠ 0 := ((GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L P sc).1
  have hT : P.stAbar sc ≠ 0 := mul_ne_zero hAb (inv_ne_zero hMo)
  have e1 : ρ - 1 + 1 = ρ := by omega
  have e2 : 2 * ρ - (ρ - 1) = ρ + 1 := by omega
  have hneg : ∀ k : ℕ, FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((-D.host.xi0) ^ k)⁻¹ =
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 ^ k)⁻¹ := by
    intro k
    rw [← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.spanSingleton_pow]
    congr 1
    congr 1
    apply FractionalIdeal.spanSingleton_eq_spanSingleton.2
    refine ⟨-1, ?_⟩
    rw [Units.smul_def]
    simp
  rw [e1, e2, hneg, hneg]
  set X := FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 with hXdef
  have hX : X ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 hx
  refine ⟨mul_ne_zero (inv_ne_zero (pow_ne_zero _ hX)) (mul_ne_zero (pow_ne_zero _ hS) (inv_ne_zero (pow_ne_zero _ hT))),
    mul_ne_zero (inv_ne_zero (pow_ne_zero _ hX)) (mul_ne_zero (pow_ne_zero _ hS) (inv_ne_zero (pow_ne_zero _ hT))), ?_⟩
  have key : (D.host.AAbar : GlobalTheory.SeeSaw.FI D) * ((X ^ ρ)⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ ρ)⁻¹))⁻¹ *
      ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ =
      FractionalIdeal.spanSingleton _ D.host.xi0⁻¹ * ((X ^ (ρ + 1))⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ (ρ + 1))⁻¹))⁻¹ := by
    rw [← FractionalIdeal.spanSingleton_inv, ← hXdef]
    have hTd : P.stAbar sc = D.host.AAbar * ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ := rfl
    rw [hTd]
    simp only [mul_inv, inv_inv, pow_succ, mul_pow]
    calc _ = (X⁻¹ * X) * (D.host.AAbar * ((X ^ ρ) * ((P.stA sc ^ ρ * P.stA sc)⁻¹ * ((D.host.AAbar : GlobalTheory.SeeSaw.FI D) ^ ρ *
          (((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) ^ ρ))) * ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) := by
          rw [inv_mul_cancel₀ hX, one_mul, mul_inv]
      _ = _ := by ring
  have hB0 : (D.host.AAbar : GlobalTheory.SeeSaw.FI D) * ((X ^ ρ)⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ ρ)⁻¹))⁻¹ ≠ 0 :=
    mul_ne_zero hAb (inv_ne_zero (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hX))
      (mul_ne_zero (pow_ne_zero _ hS) (inv_ne_zero (pow_ne_zero _ hT)))))
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.IdVGen.idV_gen D v _ hB0
  have h1 := GlobalTheory.Core.Mi.LatMatch.DiUnit.eq_one_iff.1 (GlobalTheory.Core.Mi.LatMatch.DiUnit.inv_eq_one hM)
  have hp := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v _ _ y 1 hy0 one_ne_zero hy h1
  rw [mul_one, key] at hp
  intro s
  rw [hp, hy]

end GlobalTheory.StairIdealAt
