import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GSEqZeroOfLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulPowIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)

noncomputable section

namespace GlobalTheory.GaussUnr

open ValuativeRel GlobalTheory.SplitFlip GlobalTheory.GaussNonvanish

theorem gauss_mul_unram : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {v : HeightOneSpectrum (𝓞 F)}
    (ν₀ ξ : (Fv F v)ˣ →* ℂˣ), (∀ x : (Fv F v)ˣ, (x : Fv F v) ∈ v.adicCompletionIntegers F →
      ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F → ξ x = 1) →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (ν₀ * ξ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀ ∧
      ∃ y : (Fv F v)ˣ, gauss ψ (ν₀ * ξ) = (((ξ y)⁻¹ : ℂˣ) : ℂ) * gauss ψ ν₀ := by
  intro F _ _ ψ v ν₀ ξ hξ
  have hϖ : IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have hunit : ∀ x : (Fv F v)ˣ, valuation (Fv F v) (x : Fv F v) = 1 → ξ x = 1 := fun x hx => by
    apply hξ x
    · exact (val_le_one_iff v _).1 hx.le
    · apply (val_le_one_iff v _).1
      rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  have hce : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (ν₀ * ξ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀ := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp
    congr 1
    ext c
    simp only [Set.mem_setOf_eq, CondLE]
    refine forall₂_congr fun x hx => ?_
    rw [MonoidHom.mul_apply, hunit x hx.1, mul_one]
  refine ⟨hce, ?_⟩
  unfold gauss
  rw [hce]
  generalize GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀ = c
  rcases Nat.eq_zero_or_pos c with h0 | hc1
  · subst h0
    have hsu : ∀ a b : (Res (Fv F v) 0)ˣ, a = b := fun a b =>
      Units.ext ((Ideal.Quotient.subsingleton_iff.2 (by simp)).elim _ _)
    classical
    rw [Fintype.sum_eq_single 1 (fun y hy => (hy (hsu y 1)).elim), Fintype.sum_eq_single 1 (fun y hy => (hy (hsu y 1)).elim)]
    by_cases h : ((Quotient.out (1 : (Res (Fv F v) 0)ˣ).1 : (ValuativeRel.valuation (Fv F v)).integer) : Fv F v) = 0
    · refine ⟨1, ?_⟩
      rw [dif_pos h, dif_pos h, mul_zero]
    · refine ⟨Units.mk0 _ h, ?_⟩
      rw [dif_neg h, dif_neg h, MonoidHom.mul_apply, mul_inv, Units.val_mul, mul_comm (((ν₀ _)⁻¹ : ℂˣ) : ℂ),
        mul_assoc]
  · refine ⟨1, ?_⟩
    rw [map_one, inv_one, Units.val_one, one_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : ((Quotient.out y.1 : (ValuativeRel.valuation (Fv F v)).integer) : Fv F v) = 0
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h, MonoidHom.mul_apply, hunit _ (val_rep_unit hϖ hc1 y), mul_one]

end GlobalTheory.GaussUnr
