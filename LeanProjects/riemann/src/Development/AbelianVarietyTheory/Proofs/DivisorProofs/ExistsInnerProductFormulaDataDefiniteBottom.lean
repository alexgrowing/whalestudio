import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAniso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBottomTriIs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramAtNegOfGramOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianWittIndexEqZeroDefiniteBottomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPolynomialFockThetaVectorDefiniteBottomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedInnerProductDataDefiniteBottomLargeGri
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstOneMemCuspFormsDefiniteBottomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatakeParametersConstOneDefiniteBottomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialNormalizingFactorNeZeroDefiniteBottomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialLFunctionEqNormalizingFactorDefiniteBotto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomLocalDoublingIntegralConverges
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section

namespace GlobalTheory.BottomIPData

theorem data_exists : GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → A.SigOK → ∀ t : T,
  ∃ (χA χB : (AE D)ˣ →* Circle) (sA : RealMat (GlobalTheory.Grid.neg A)) (sB : RealMat WW) (cA : CptF (GlobalTheory.Grid.neg A))
    (a : GL (Fin (GlobalTheory.Grid.neg A).rank) (AE D)) (νW : Measure (WO (GlobalTheory.Grid.neg A) WW)) (𝓕W : Set (WO (GlobalTheory.Grid.neg A) WW))
    (LA : Lat (GlobalTheory.Grid.neg A)) (LB : Lat WW) (Sf : Finset (FinPl D)) (par : GlobalTheory.LFun.Fam D.host.E) (κ : ℂ) (P : PolF D WW.rank A.rank),
    Pair W.ψ W.θ (GlobalTheory.Grid.neg A) WW χA χB sA sB A'.rank cA a ((X.ω t).toSgn true) νW 𝓕W ∧ wittIndex WW = 0 ∧
    IsFockVec W.ψ W.θ (GlobalTheory.Grid.neg A) WW sA sB (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) ∧ Unram W.ψ (GlobalTheory.Grid.neg A) WW χB LA LB Sf (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) ∧
    (fun _ => (1 : ℂ)) ∈ A0 W.θ (GlobalTheory.Grid.neg A) cA ∧
    GlobalTheory.LFun.IsParamFun D.sp.cm.sig (GlobalTheory.Grid.neg A).gram LA (Sf : Set (FinPl D)) (fun _ => (1 : ℂ)) par ∧
    SphFun (GlobalTheory.Grid.neg A) LA Sf (fun _ => (1 : ℂ)) ∧ κ ≠ 0 ∧
    GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) ≠ 0 ∧
    (∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ →
      HolValueAt (fun s => GlobalTheory.LFun.LSD D Sf par χB (s + 1 / 2)) ((A'.rank : ℂ) / 2)
        (κ * GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) *
          ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s)) ∧
    ∀ m : Measure (GA D (GlobalTheory.Grid.neg A)), m.IsHaarMeasure →
      (∃ s₁ : ℝ, s₁ < (A'.rank : ℝ) / 2 ∧ IntegrableOn
        (integrand ((X.ω t).toSgn true) m νW 𝓕W LA a (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (fun _ => 1) (fun _ => 1) s₁) (openOff (GlobalTheory.Grid.neg A) LA Sf) m) ∧
      ∫ g in openOff (GlobalTheory.Grid.neg A) LA Sf, wcoef ((X.ω t).toSgn true) νW 𝓕W (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) g * rcoef m (fun _ => 1) (fun _ => 1) g ∂m ≠ 0 := by
  have H := gbig_and GlobalTheory.BottomPairData.pair_data (gbig_and GlobalTheory.T.hermitianWittIndex_eq_zero_definiteBottom (gbig_and GlobalTheory.T.isPolynomialFockThetaVector_definiteBottom (gbig_and GlobalTheory.BottomIPData.unram_bottom (gbig_and GlobalTheory.T.const_one_mem_cuspForms_definiteBottom
    (gbig_and GlobalTheory.T.exists_satakeParameters_const_one_definiteBottom (gbig_and GlobalTheory.T.partialNormalizingFactor_ne_zero_definiteBottom (gbig_and GlobalTheory.T.partialLFunction_eq_normalizingFactor_definiteBottom GlobalTheory.T.definiteBottom_localDoublingIntegral_converges)))))))
  refine gbig_mono H ?_
  intro D T Lc sc G μ₀ C x b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ W i j A A' WW X hX hA t
  obtain ⟨cA, a, νW, 𝓕W, hP⟩ := h1 W i j A A' WW X hX hA t
  obtain ⟨par, hpar⟩ := h6 W i j A A' WW X hX t
  obtain ⟨κ, hκ, hL⟩ := h8 W i j A A' WW X hX t par hpar
  obtain ⟨P, hloc⟩ := h9 W i j A A' WW X hX t cA a νW 𝓕W hP
  refine ⟨betaB G i j, betaB G i j / alphaB Lc i j t, fun τ => -X.rA.s τ, X.rW.s, cA, a, νW, 𝓕W, X.rA.Λ, X.rW.Λ,
    sfB G t, par, κ, P, hP, h2 W i j A A' WW X hX t, h3 W i j A A' WW X hX t P, h4 W i j A A' WW X hX t P,
    h5 W i j A A' WW X hX t cA hP.setting, hpar, ?_, hκ, h7 W i j A A' WW X hX t, hL, hloc⟩
  intro v _ k _ g
  rfl

end GlobalTheory.BottomIPData

end
