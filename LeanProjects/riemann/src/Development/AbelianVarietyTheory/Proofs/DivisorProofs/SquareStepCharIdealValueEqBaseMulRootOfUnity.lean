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

namespace GlobalTheory.SqStepIdeal

open GlobalTheory.LFun

theorem val_mem {D : D7} {χ : HChar D.host.E} {n : ℕ} (h1 : χ.OrderDvd n) (h2 : LocIn D.what₂.embLL χ)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) :
    χ.val w ^ n = 1 ∧ ((χ.val w : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
  refine ⟨?_, ?_⟩
  · have e1 : (χ.1 : _ →* ℂˣ) ^ n = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    have e2 : ∀ y, χ.1 y ^ n = 1 := fun y => by
      have := DFunLike.congr_fun e1 y
      simpa [MonoidHom.pow_apply] using this
    exact e2 _
  · obtain ⟨y, hy⟩ := h2 w (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w))
    exact ⟨y, hy⟩

theorem mulSupport_finite {E : Type} [Field E] [NumberField E] (f : IsDedekindDomain.HeightOneSpectrum (𝓞 E) → ℂˣ)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    (Function.mulSupport fun w => f w ^ FractionalIdeal.count E w 𝔞).Finite := by
  refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors 𝔞)).subset fun w hw => ?_
  intro h
  apply hw
  simp only [h, zpow_zero]

theorem idealVal_chs_base : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), ∃ b : D.what₂.LL, (∃ n : ℕ, 0 < n ∧ b ^ n = 1) ∧
      ((idealVal (GlobalTheory.SqStep.chs G i j μ₀).ν 𝔞 : ℂˣ) : ℂ) = D.what₂.embLL b * ((idealVal (GlobalTheory.SqStep.chs G i j t).ν 𝔞 : ℂˣ) : ℂ) := by
  intro D T Lc sc G μ₀ hL W S hN i j t 𝔞
  have e : ∀ s, (GlobalTheory.SqStep.chs G i j s).ν = G.nu s i (j + 1) := fun s => by
    show (Lc.mu s (j + 1) * Lc.eta ^ _) / (G.ch.chi _ * Lc.eta ^ _) = _
    rw [mul_div_mul_right_eq_div]
    rfl
  have hν : (GlobalTheory.SqStep.chs G i j μ₀).ν = (GlobalTheory.SqStep.chs G i j t).ν * ((Lc.xi t)⁻¹ * Lc.xi μ₀) := by
    rw [e, e]
    refine MonoidHom.ext fun x => ?_
    show Lc.mu0 (j + 1) x * Lc.xi μ₀ x / G.ch.chi (D.R.m - i) x =
      Lc.mu0 (j + 1) x * Lc.xi t x / G.ch.chi (D.R.m - i) x * ((Lc.xi t x)⁻¹ * Lc.xi μ₀ x)
    rw [div_mul_eq_mul_div, mul_assoc (Lc.mu0 (j + 1) x) (Lc.xi t x), mul_inv_cancel_left]
  obtain ⟨n, hn, hfin⟩ := hL.xi_fin t
  let c : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := fun w => ((Lc.xiH t).val w)⁻¹
  have hw : ∀ w, val (GlobalTheory.SqStep.chs G i j μ₀).ν w = val (GlobalTheory.SqStep.chs G i j t).ν w * c w := fun w => by
    rw [hν, val_mul, val_mul, val_inv, val_eq_of_chrEq (hL.xi t) w, val_eq_of_chrEq (hL.xi μ₀) w, hL.xi_base]
    rw [show (1 : HChar D.host.E).val w = 1 from rfl, mul_one]
  let H : Subgroup ℂˣ :=
    { carrier := {z | z ^ n = 1 ∧ (z : ℂ) ∈ D.what₂.embLL.fieldRange}
      mul_mem' := fun ha hb => ⟨by rw [mul_pow, ha.1, hb.1, one_mul], by rw [Units.val_mul]; exact mul_mem ha.2 hb.2⟩
      one_mem' := ⟨one_pow _, by rw [Units.val_one]; exact one_mem _⟩
      inv_mem' := fun ha => ⟨by rw [inv_pow, ha.1, inv_one], by rw [Units.val_inv_eq_inv_val]; exact inv_mem ha.2⟩ }
  have hc : ∀ w, c w ∈ H := fun w => H.inv_mem (val_mem hfin (hN.chars.xi t) w)
  have hprod : idealVal (GlobalTheory.SqStep.chs G i j μ₀).ν 𝔞 =
      idealVal (GlobalTheory.SqStep.chs G i j t).ν 𝔞 * ∏ᶠ w, c w ^ FractionalIdeal.count D.host.E w 𝔞 := by
    unfold idealVal
    simp_rw [hw, mul_zpow]
    exact finprod_mul_distrib (mulSupport_finite _ 𝔞) (mulSupport_finite _ 𝔞)
  have hz : ∏ᶠ w, c w ^ FractionalIdeal.count D.host.E w 𝔞 ∈ H := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := (mulSupport_finite c 𝔞).toFinset) (by simp)]
    exact H.prod_mem fun w _ => H.zpow_mem (hc w) _
  obtain ⟨hzn, hzr⟩ := hz
  obtain ⟨b, hb⟩ := RingHom.mem_fieldRange.1 hzr
  refine ⟨b, ⟨n, hn, ?_⟩, ?_⟩
  · apply D.what₂.embLL.injective
    rw [map_pow, hb, map_one, ← Units.val_pow_eq_pow_val, hzn, Units.val_one]
  · rw [hprod, Units.val_mul, hb, mul_comm]

end GlobalTheory.SqStepIdeal
