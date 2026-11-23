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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalGaussSumIntegerDvdResidueCardPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
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

namespace GlobalTheory.TwistGaussInt

theorem gauss_dvd : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (W : G.Weil) (S : GridChoice W Set.univ) {μ₀ : T},
    Lc.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)}
      (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (ψ : AddChar (AF D.host.F) ℂ), PsiUnr ψ v →
      GlobalTheory.AdelicU.splitPrime τ ∈ locPl G t → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (chrW (GlobalTheory.SqStep.chs G i j t).ν τ) = 1 →
      ∃ g : 𝓞 D.what₂.LL, D.what₂.embLL (g : D.what₂.LL) = gauss ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν τ) ∧
        g ∣ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.what₂.LL) := by
  intro D T Lc sc G W S μ₀ hL hN i j t v τ ψ hψ hloc hc
  set ν := chrW (GlobalTheory.SqStep.chs G i j t).ν τ with hν
  have hval : ∀ x : (Fv D.host.F v)ˣ, (ν x : ℂ) = ((nuH G t i j).loc (GlobalTheory.AdelicU.splitPrime τ)
      (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom x) : ℂ) := fun x => by
    rw [hν, GlobalTheory.SqStepArith.chrW_chs G hL]
  have hcont : Continuous (fun x : (Fv D.host.F v)ˣ => (ν x : ℂ)) := by
    have h1 : Continuous ((nuH G t i j).loc (GlobalTheory.AdelicU.splitPrime τ)) :=
      (nuH G t i j).2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele _)
    have h2 := Continuous.units_map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom
      (GlobalTheory.LFun.SplitChart.continuous_complMap (GlobalTheory.AdelicU.splitPrime_under τ))
    have := Units.continuous_val.comp (h1.comp h2)
    refine this.congr fun x => ?_
    rw [hval]; rfl
  have hnorm : ∀ x, ‖(ν x : ℂ)‖ = 1 := fun x => by
    show ‖((Circle.toUnits _ : ℂˣ) : ℂ)‖ = 1
    exact Circle.norm_coe _
  have hrange : ∀ x : (Fv D.host.F v)ˣ, (ν x : ℂ) ∈ Set.range D.what₂.embLL := by
    intro x
    rw [hval]
    generalize Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom x = y
    have hm : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
    have e : ((nuH G t i j).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ) =
        ((Lc.C.mu0 j).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ) * ((Lc.xiH t).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ) / ((G.ch.chiH (D.R.m - i)).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ) := by
      simp [nuH, Formalism.L2.Host.HChar.loc, div_eq_mul_inv]
    rw [e]
    have r1 := hN.chars.mu0 j (GlobalTheory.AdelicU.splitPrime τ) y
    have r2 := hN.chars.xi t (GlobalTheory.AdelicU.splitPrime τ) y
    have r3 := hN.chars.chi (D.R.m - i) hm (Nat.sub_le _ _) (GlobalTheory.AdelicU.splitPrime τ) y
    rw [← RingHom.coe_fieldRange] at r1 r2 r3 ⊢
    exact div_mem (mul_mem r1 r2) r3
  have hroots : ∀ ζ : ℂ, ζ ^ (Ideal.absNorm v.asIdeal ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν) = 1 → ζ ∈ Set.range D.what₂.embLL := by
    intro ζ hζ
    rw [hc, pow_one] at hζ
    apply hN.roots t _ hloc
    rw [GlobalTheory.LFun.SplitChart.absNorm_splitPrime]
    have hd : 1 ≤ depthAt G (GlobalTheory.AdelicU.splitPrime τ) := le_max_right _ _
    obtain ⟨k, hk⟩ : ∃ k, depthAt G (GlobalTheory.AdelicU.splitPrime τ) = k + 1 := ⟨_, (Nat.sub_add_cancel hd).symm⟩
    rw [hk, pow_succ, pow_mul', hζ, one_pow]
  obtain ⟨g, g', hg, hgg⟩ := GlobalTheory.T.localGaussSum_integer_dvd_residueCard_pow D.what₂.embLL ψ v ν hψ hcont hnorm (by rw [hc]) (fun x _ _ => hrange x) hroots
  refine ⟨g, hg, ⟨g', ?_⟩⟩
  rw [hgg, hc, pow_one]

end GlobalTheory.TwistGaussInt
