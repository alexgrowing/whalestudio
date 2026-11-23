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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsMulOfCondExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Mu0ChiHUnramifiedOutsideStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceStepCharacterConductorExponentOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussSumStepCharacterTwistPlaceDvdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepCharacterUniformiserValueUnitAwayTwistStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

namespace GlobalTheory.SqTwist

theorem twist_factor : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T)
    (Bs : Base D.host.F D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs → ∀ (v : Bs.P), v.1 ∈ (GlobalTheory.SqStep.chs G i j t).T →
    v.1 ∉ G.pl.S0 → ∀ (s : ℤˣ) (z : ℤ), ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) ≠ 0 → ∃ b : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) b ∧
      D.what₂.embLL b * ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) = 1 := by
  intro D T Lc sc G μ₀ hL W S hN i j t Bs hB v hvT hvS s z hf
  classical
  set τ := Bs.τ v with hτ
  set w := GlobalTheory.AdelicU.splitPrime τ with hw
  have hunder : w.under (𝓞 D.host.F) = v.1 := GlobalTheory.AdelicU.splitPrime_under τ
  have hloc : w ∈ locPl G t := hB.2.2.2 v hvT
  have hW0 : w ∉ G.pl.W0 := by
    intro h
    obtain ⟨u, hu, hu'⟩ := Finset.mem_image.1 h
    apply hvS
    have := G.pl.under_w hu
    rw [hu'] at this
    rw [← hunder, this]
    exact hu
  have htw : w ∈ twPl G t := Finset.mem_filter.2 ⟨hloc, hW0⟩
  have hQ : w ∈ Lc.Q t := by
    rcases Finset.mem_union.1 hloc with h | h
    · exact absurd h hW0
    · exact h
  have hq : Ideal.absNorm w.asIdeal = Ideal.absNorm v.1.asIdeal := GlobalTheory.LFun.SplitChart.absNorm_splitPrime τ
  have hQn : 0 < Qn G t := by
    unfold Qn
    refine Finset.prod_pos fun u _ => Nat.pos_of_ne_zero ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact u.ne_bot
  have hqd : Ideal.absNorm v.1.asIdeal ∣ Qn G t := hq ▸ Finset.dvd_prod_of_mem _ htw
  obtain ⟨hmu, hchi⟩ := GlobalTheory.T.mu0_and_chiH_unrAt_outside_S0 G hL i j t w hQ (by rw [hunder]; exact hvS)
  have hc := GlobalTheory.T.twistPlace_stepCharacter_conductorExponent_one G hL i j t τ hmu hchi hQ
  obtain ⟨g, hg, hgd⟩ := GlobalTheory.T.gaussSum_stepCharacter_twistPlace_dvd G W S hL hN i j t τ Bs.ψ (hB.2.2.1 v.1 v.2) hloc hc
  obtain ⟨x, hx, hxa⟩ := GlobalTheory.T.stepCharacter_uniformiserValue_unit_away_twist G W S hL hN i j t τ hmu hchi htw
  set ν := chrW (GlobalTheory.SqStep.chs G i j t).ν τ with hν
  set s' : (Fv D.host.F v.1)ˣ := Units.map (Int.castRingHom _).toMonoidHom s with hs'

  have hs2 : s' ^ 2 = 1 := by
    rw [hs', ← map_pow, Int.units_sq, map_one]
  have hsgn : ((ν s' : ℂˣ) : ℂ) = 1 ∨ ((ν s' : ℂˣ) : ℂ) = -1 := by
    have h2 : ((ν s' : ℂˣ) : ℂ) * ((ν s' : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, ← map_mul, ← sq, hs2, map_one, Units.val_one]
    exact mul_self_eq_one_iff.1 h2
  obtain ⟨e, he, hea⟩ : ∃ e : D.what₂.LL, D.what₂.embLL e = ((ν s' : ℂˣ) : ℂ) ∧ GlobalTheory.Square.IsAwayUnit (Qn G t) e := by
    rcases hsgn with h | h
    · exact ⟨1, by rw [map_one, h], GlobalTheory.Square.AwayClosure.of_pow_eq_one _ one_pos (one_pow 1)⟩
    · exact ⟨-1, by rw [map_neg, map_one, h], GlobalTheory.Square.AwayClosure.of_pow_eq_one _ two_pos (by norm_num)⟩

  set q : ℕ := Ideal.absNorm v.1.asIdeal with hqdef
  have hqa : GlobalTheory.Square.IsAwayUnit (Qn G t) ((q : D.what₂.LL) ^ (-z)) := by
    have hn : ∀ n : ℕ, GlobalTheory.Square.IsAwayUnit (Qn G t) ((q : D.what₂.LL) ^ n) := by
      intro n
      have h1 : (((q : 𝓞 D.what₂.LL) ^ n : 𝓞 D.what₂.LL) : D.what₂.LL) = (q : D.what₂.LL) ^ n := by
        simp only [RingOfIntegers.coe_eq_algebraMap, map_pow, map_natCast]
      rw [← h1]
      apply GlobalTheory.Square.AwayClosure.of_dvd (k := n)
      exact pow_dvd_pow_of_dvd (Nat.cast_dvd_cast hqd) n
    rcases Int.eq_nat_or_neg (-z) with ⟨n, hn' | hn'⟩
    · rw [hn', zpow_natCast]; exact hn n
    · rw [hn', zpow_neg, zpow_natCast]; exact GlobalTheory.Square.AwayClosure.inv hQn (hn n)
  have hga : GlobalTheory.Square.IsAwayUnit (Qn G t) (g : D.what₂.LL) :=
    GlobalTheory.Square.AwayClosure.of_dvd (k := 1) (by rw [pow_one]; exact hgd.trans (Nat.cast_dvd_cast hqd))
  set a : D.what₂.LL := e * ((q : D.what₂.LL) ^ (-z) * (g : D.what₂.LL) * x) with ha
  have haA : GlobalTheory.Square.IsAwayUnit (Qn G t) a :=
    GlobalTheory.Square.AwayClosure.mul hea (GlobalTheory.Square.AwayClosure.mul (GlobalTheory.Square.AwayClosure.mul hqa hga) hxa)
  have hfa : D.what₂.embLL a = ((ν s' : ℂˣ) : ℂ) * eps Bs.ψ ν z := by
    rw [ha]
    unfold eps
    rw [hc]
    simp only [map_mul, map_zpow₀, map_natCast, he, hg, hx, Nat.cast_one, pow_one]
    congr 1
    rw [neg_one_mul]
  refine ⟨a⁻¹, GlobalTheory.Square.AwayClosure.inv hQn haA, ?_⟩
  rw [map_inv₀, ← hfa]
  rw [← hfa] at hf
  exact inv_mul_cancel₀ hf

end GlobalTheory.SqTwist
