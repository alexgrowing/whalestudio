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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterAtUniformizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSubOneMemPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfUnitOffEmbedding
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

namespace GlobalTheory.TwistStepVal

theorem isAwayUnit_loc {L K : Type} [Field L] [NumberField L] [Field K] [NumberField K] (σ : K →+* ℂ)
    (χ : Formalism.L2.Host.HChar L) {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n : I → ℤ} (hinf : χ.HasInf φ n)
    {w : HeightOneSpectrum (𝓞 L)} (hw : χ.UnrAt w) (y : (w.adicCompletion L)ˣ) (hy : Formalism.L2.Host.IsUnifAt w y)
    {m : ℕ} (hm : Ideal.absNorm w.asIdeal ∣ m) {x : K} (hx : σ x = ((χ.loc w y : ℂˣ) : ℂ)) :
    GlobalTheory.Square.IsAwayUnit m x := by
  have hq : 0 < Ideal.absNorm w.asIdeal :=
    Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  refine GlobalTheory.Square.isAwayUnit_of_unitOff_embedding σ x _ m hq hm ?_
  rw [hx, Formalism.L2.Host.HChar.val_eq χ hw y hy]
  exact GlobalTheory.ValUnitLevel.unitOff_val L χ I φ n w _ hinf hw (Ideal.absNorm_mem _)

theorem step_val : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (W : G.Weil) (S : GridChoice W Set.univ) {μ₀ : T},
    Lc.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)}
      (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
      (Lc.C.mu0 j).UnrAt (GlobalTheory.AdelicU.splitPrime τ) → (G.ch.chiH (D.R.m - i)).UnrAt (GlobalTheory.AdelicU.splitPrime τ) →
      GlobalTheory.AdelicU.splitPrime τ ∈ twPl G t →
      ∃ x : D.what₂.LL, D.what₂.embLL x = ((chrW (GlobalTheory.SqStep.chs G i j t).ν τ (unifAt v) : ℂˣ) : ℂ) ∧
        GlobalTheory.Square.IsAwayUnit (Qn G t) x := by
  intro D T Lc sc G W S μ₀ hL hN i j t v τ hμ hχ htw
  rw [GlobalTheory.SqStepArith.chrW_chs G hL]
  have hy : Formalism.L2.Host.IsUnifAt (GlobalTheory.AdelicU.splitPrime τ)
      (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom (unifAt v)) := by
    show Valued.v (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ) ((unifAt v : (Fv D.host.F v)ˣ) : Fv D.host.F v))
      = WithZero.exp (-1 : ℤ)
    rw [GlobalTheory.LFun.SplitTie.valued_complMap τ (GlobalTheory.AdelicU.splitPrime_under τ), GlobalTheory.ChrWUnif.valued_unifAt]
  generalize Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom (unifAt v) = y at hy ⊢
  have hm : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have e : ((nuH G t i j).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ) =
      ((Lc.C.mu0 j).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ) * ((Lc.xiH t).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ) *
        ((G.ch.chiH (D.R.m - i)).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ)⁻¹ := by
    simp [nuH, Formalism.L2.Host.HChar.loc, div_eq_mul_inv]
  obtain ⟨a, ha⟩ := hN.chars.mu0 j (GlobalTheory.AdelicU.splitPrime τ) y
  obtain ⟨b, hb⟩ := hN.chars.xi t (GlobalTheory.AdelicU.splitPrime τ) y
  obtain ⟨c, hc⟩ := hN.chars.chi (D.R.m - i) hm (Nat.sub_le _ _) (GlobalTheory.AdelicU.splitPrime τ) y
  have hQ : 0 < Qn G t := Finset.prod_pos fun w _ =>
    Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hdvd : Ideal.absNorm (GlobalTheory.AdelicU.splitPrime τ).asIdeal ∣ Qn G t :=
    Finset.dvd_prod_of_mem (fun w : HeightOneSpectrum (𝓞 D.host.E) => Ideal.absNorm w.asIdeal) htw
  refine ⟨a * b * c⁻¹, by rw [e, map_mul, map_mul, map_inv₀, ha, hb, hc], ?_⟩
  obtain ⟨n, -, hn⟩ := (Lc.C.isMu0 j).inf
  have ua := isAwayUnit_loc D.what₂.embLL _ hn hμ y hy hdvd ha
  have uc := isAwayUnit_loc D.what₂.embLL _ (G.ch.inf _ hm (Nat.sub_le _ _)) hχ y hy hdvd hc
  obtain ⟨k, hk, hξ⟩ := hL.xi_fin t
  have ub : GlobalTheory.Square.IsAwayUnit (Qn G t) b := by
    refine GlobalTheory.Square.AwayClosure.of_pow_eq_one _ hk (D.what₂.embLL.injective ?_)
    rw [map_pow, hb, map_one, ← Units.val_pow_eq_pow_val]
    have h1 : (Lc.xiH t ^ k).loc (GlobalTheory.AdelicU.splitPrime τ) y = 1 := by
      rw [show Lc.xiH t ^ k = 1 from hξ]; rfl
    rw [← Units.val_one, ← h1]
    simp [Formalism.L2.Host.HChar.loc]
  exact GlobalTheory.Square.AwayClosure.mul (GlobalTheory.Square.AwayClosure.mul ua ub) (GlobalTheory.Square.AwayClosure.inv hQ uc)

end GlobalTheory.TwistStepVal
