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

namespace GlobalTheory.CondLESplit

open ValuativeRel

theorem isEquiv_Fv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (valuation (Fv F v)).IsEquiv (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))) := by
  have : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact isEquiv (valuation (Fv F v)) (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))

theorem valued_unifAt {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) = WithZero.exp (-1 : ℤ) := by
  have he := isEquiv_Fv v
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπ' : Valued.v ((π : F) : Fv F v) = WithZero.exp (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation']; exact hπ
  have hlt : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) < 1 :=
    he.lt_one_iff_lt_one.1 (hϖ ▸ uniformizer_lt_one)
  apply le_antisymm
  · have h0 : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) ≠ 0 := by simp
    rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega
  · rw [← hπ']
    have hπ1 : valuation (Fv F v) ((π : F) : Fv F v) < 1 := by
      refine he.lt_one_iff_lt_one.2 ?_
      rw [hπ', ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    exact (he _ _).1 (hϖ ▸ le_uniformizer_iff.2 hπ1)

end GlobalTheory.CondLESplit

open GlobalTheory.CondLESplit in
theorem GlobalTheory.CondLESplit.condLE_iff : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) (ρ : ((GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)ˣ →* ℂˣ) (n : ℕ),
    GlobalTheory.SplitFlip.CondLE (unifAt v) n (ρ.comp (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom)) ↔
      ∀ x : ((GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)ˣ, Formalism.L2.Host.IsUnitAt (GlobalTheory.AdelicU.splitPrime τ) x →
        Valued.v ((x : (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E) - 1) ≤ WithZero.exp (-(n : ℤ)) → ρ x = 1 := by
  intro F E _ _ _ _ _ v τ ρ n
  set hw := GlobalTheory.AdelicU.splitPrime_under τ
  set f := GlobalTheory.LFun.complMap hw
  have he := isEquiv_Fv v
  have hval : ∀ a : Fv F v, Valued.v (f a) = Valued.v a := GlobalTheory.LFun.SplitTie.valued_complMap τ hw
  have hbij : Function.Bijective f := GlobalTheory.LFun.SplitTie.complMap_bijective τ hw
  have key : ∀ y : (Fv F v)ˣ, y ∈ GlobalTheory.SplitFlip.unitCong (unifAt v ^ n) ↔
      (Formalism.L2.Host.IsUnitAt (GlobalTheory.AdelicU.splitPrime τ) (Units.map f.toMonoidHom y) ∧
        Valued.v (((Units.map f.toMonoidHom y : ((GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)ˣ) :
          (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E) - 1) ≤ WithZero.exp (-(n : ℤ))) := by
    intro y
    have h1 : ((Units.map f.toMonoidHom y : ((GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)ˣ) :
        (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E) = f y := rfl
    have hp : Valued.v (((unifAt v ^ n : (Fv F v)ˣ)) : Fv F v) = WithZero.exp (-(n : ℤ)) := by
      rw [Units.val_pow_eq_pow_val, map_pow, valued_unifAt, ← WithZero.exp_nsmul]
      congr 1; simp
    show (ValuativeRel.valuation (Fv F v) (y : Fv F v) = 1 ∧ ValuativeRel.valuation (Fv F v) ((y : Fv F v) - 1) ≤
        ValuativeRel.valuation (Fv F v) (((unifAt v ^ n : (Fv F v)ˣ)) : Fv F v)) ↔ _
    unfold Formalism.L2.Host.IsUnitAt
    rw [h1, he.eq_one_iff_eq_one, he, hp, ← map_one f, ← map_sub, hval, hval]
  constructor
  · intro h x hx1 hx2
    obtain ⟨a, ha⟩ := hbij.2 (x : (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)
    have ha0 : a ≠ 0 := by
      rintro rfl; rw [map_zero] at ha; exact x.ne_zero ha.symm
    set y := Units.mk0 a ha0
    have hy : Units.map f.toMonoidHom y = x := Units.ext ha
    have := h y ((key y).2 (hy ▸ ⟨hx1, hx2⟩))
    rw [← hy]; exact this
  · intro h y hy
    exact h _ ((key y).1 hy).1 ((key y).1 hy).2
