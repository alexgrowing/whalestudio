import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsGridFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleHypothesesOfStandingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeCharMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankSumLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAbovePlaceOfTrivialUnits
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.PsiDifferent

open GlobalTheory.Idele WithZero
open scoped nonZeroDivisors
open GlobalTheory.StdDual (codiff codiff_ne_zero)

theorem not_dvd_different_of_psiUnr : ∀ {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ},
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {v : HeightOneSpectrum (𝓞 F)}, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr ψ v →
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := by
  intro F _ _ ψ hψ v hU hdvd
  have h0 : differentIdeal ℤ (𝓞 F) ≠ 0 := differentIdeal_ne_bot
  have hD : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (codiff F)⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have hcnt := FractionalIdeal.count_coe F v h0
  rw [hD, FractionalIdeal.count_inv] at hcnt
  have hne := (Associates.count_ne_zero_iff_dvd h0 v.irreducible).2 hdvd
  set c := FractionalIdeal.count F v (codiff F) with hc
  have hc1 : c ≤ -1 := by omega
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set x : Fv F v := algebraMap F (Fv F v) (π ^ c) with hx
  have hval : Valued.v x = WithZero.exp (-c) := by
    rw [hx, valued_algebraMap, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul]
    congr 1; ring
  have hmem : GlobalTheory.AdelicU.singleFin v x ∈ adelicIdeal (codiff F) := by
    refine (mem_adelicIdeal_iff codiff_ne_zero).2 fun u => ?_
    by_cases hu : u = v
    · subst hu
      rw [show (GlobalTheory.AdelicU.singleFin u x) u = x from GlobalTheory.AdelicU.evalV_singleFin_self u x, hval]
    · rw [show (GlobalTheory.AdelicU.singleFin v x) u = 0 from GlobalTheory.AdelicU.evalV_singleFin_ne hu x, map_zero]
      exact zero_le'
  rw [GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.PsiNontriv.isStd_fin_rat hψ)] at hmem
  have hint : x ∈ v.adicCompletionIntegers F := by
    refine (hU x).1 fun y hy => ?_
    have hα : ∀ u, (GlobalTheory.AdelicU.singleFin v y) u ∈ u.adicCompletionIntegers F := by
      intro u
      by_cases hu : u = v
      · subst hu
        rw [show (GlobalTheory.AdelicU.singleFin u y) u = y from GlobalTheory.AdelicU.evalV_singleFin_self u y]
        exact hy
      · rw [show (GlobalTheory.AdelicU.singleFin v y) u = 0 from GlobalTheory.AdelicU.evalV_singleFin_ne hu y]
        exact zero_mem _
    have e : GlobalTheory.AdelicU.singleFin v y * GlobalTheory.AdelicU.singleFin v x = GlobalTheory.AdelicU.singleFin v (x * y) := by
      apply GlobalTheory.AdelicU.af_ext
      intro u
      by_cases hu : u = v
      · subst hu
        rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self,
          GlobalTheory.AdelicU.evalV_singleFin_self, mul_comm]
      · rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu,
          GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
    have := hmem _ hα
    rw [e] at this
    exact this
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval, ← WithZero.exp_zero, WithZero.exp_le_exp] at hint
  omega

end GlobalTheory.PsiDifferent

end
