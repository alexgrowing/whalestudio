import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DownRight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterFiniteOrderValuesInField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem chrEq_pow' {D : D7} {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) (a : ℕ) :
    ChrEq (c ^ a) (χ ^ a) := by
  refine ⟨⟨?_, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · have : ((c ^ a : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => c x ^ a := by
      funext x; simp
    rw [this]
    exact h.1.1.pow a
  · have h1 := h.1.2 x
    simp only [MonoidHom.pow_apply, h1, one_pow]
  · have hp : (χ ^ a).locK P k = χ.locK P k ^ a := by
      have : ∀ x, (χ ^ a).1 x = χ.1 x ^ a := fun x => by rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]
      exact this _
    rw [MonoidHom.pow_apply, hp, Units.val_pow_eq_pow_val, ← h.2 P e he k x hx]
    exact map_pow Circle.coeHom _ _

private theorem exists_prime_power_pow_eq_one {D : D7} {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) {n : ℕ}
    (hn : χ.OrderDvd n) : c ^ n = 1 := by
  have h1 := chrEq_pow' h n
  rw [show χ ^ n = 1 from hn] at h1
  exact MonoidHom.ext fun x => GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 x

theorem _root_.GlobalTheory.T.squareNu_ratio_values_roots_of_unity : GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ →
    ∀ (i j : Fin D.R.m) (t : T) (k : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)ˣ), ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧
      (((GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) = D.what₂.embLL ζ := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D _ _ _ _ T Lc μ₀ hL G W S hN i j t k => ?_⟩⟩
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have hc1 : Lc.xi μ₀ k = 1 := GlobalTheory.ChrEqUnique.eq_one_of_chrEq (hL.xi_base ▸ hL.xi μ₀) k
  have e : (GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k = Lc.xi t k := by
    have key : ∀ {Γ : Type} [CommGroup Γ] (a x y e c : Γ), y = 1 → (a * x * e / (c * e)) / (a * y * e / (c * e)) = x := by
      intro Γ _ a x y e c hy
      subst hy
      rw [mul_one, div_div_div_cancel_right, mul_div_mul_right_eq_div, mul_div_cancel_left]
    exact key (Lc.mu0 ((j : ℕ) + 1) k) (Lc.xi t k) (Lc.xi μ₀ k) ((Lc.eta ^ (rankV D i j % 2)) k) (G.ch.chi (D.R.m - i) k) hc1
  obtain ⟨y, hy⟩ := GlobalTheory.Adopt.heckeCharacter_finiteOrder_values_in_field D (Lc.xi t) (Lc.xiH t) n _ D.what₂.embLL (hL.xi t) hn ho ((hN.chars.xi t).valuesIn) k
  have h1 : ((Lc.xi t k : Circle) : ℂ) ^ n = 1 := by
    have := DFunLike.congr_fun (exists_prime_power_pow_eq_one (hL.xi t) ho) k
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this
    exact (map_pow Circle.coeHom _ _).symm.trans (congrArg _ this)
  have hyn : (y : D.what₂.LL) ^ n = 1 := D.what₂.embLL.injective (by rw [map_pow, hy, h1, map_one])
  exact ⟨y, GlobalTheory.KappaArith.isAwayUnit_of_pow_eq_one _ hn hyn, by rw [e, hy]⟩
