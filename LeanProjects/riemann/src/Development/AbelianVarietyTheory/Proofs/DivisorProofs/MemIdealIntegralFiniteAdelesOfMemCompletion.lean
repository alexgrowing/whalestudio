import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IpEqZeroOfHeisEigen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumeratorIdealOfAntiInvariantDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharEqOfFinitePartPowerInverse

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

namespace GlobalTheory.CosetOrth

theorem mem_hatId_of_inHat : ∀ {D : D7} (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ x : Formalism.MainNotions.StandardLatticesGL3.AE D,
  InHat (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (GlobalTheory.BotFormula.toFinE D x) → x ∈ hatId D 𝔪 := by
  intro D 𝔪 h𝔪 x hx
  have hI : (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔪
  have hN : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔪)
  obtain ⟨a, s, hs, e⟩ := GlobalTheory.Mem.Col2.SplitChar.exists_approx x hN
  have hNm : ((Ideal.absNorm 𝔪 : ℕ) : D.host.E) ∈ (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.absNorm_mem 𝔪, map_natCast _ _⟩
  have ha : a ∈ (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    refine (GlobalTheory.NumeratorIdeal.mem_iff_valuation D.host.E hI a).2 fun w => ?_
    rw [← GlobalTheory.Mem.Col2.SplitChar.vl_inc, eq_sub_of_add_eq e.symm]
    refine Valuation.map_sub_le _ ?_ ?_
    · rw [GlobalTheory.Mem.Col2.SplitChar.vl_apply, GlobalTheory.NormRatio.ChrFin.adEquiv_eq]
      exact hx w
    · rw [map_mul, GlobalTheory.Mem.Col2.SplitChar.vl_nat]
      exact (mul_le_of_le_one_right' (GlobalTheory.Mem.Col2.SplitChar.vl_le hs w)).trans
        ((GlobalTheory.NumeratorIdeal.mem_iff_valuation D.host.E hI _).1 hNm w)
  obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
  rw [e]
  refine add_mem (AddSubgroup.subset_closure ⟨b, hb, 1, one_mem _, (mul_one _).symm⟩)
    (AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem 𝔪, s, hs, ?_⟩)
  exact congrArg (· * s) (map_natCast ((Formalism.MainNotions.StandardLatticesGL3.inc D).comp (algebraMap (𝓞 D.host.E) D.host.E)) _).symm

end GlobalTheory.CosetOrth
