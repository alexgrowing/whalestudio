import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitNDgOfLocalOfSteps
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKA

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd

variable {D : D7} {n : ℕ}

def MatchGenA (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (μ : Measure (Mx D V.rank n)) (lam : Measure (hermA D n))
    (nb : hermA D n → G D n) (w : G D n) (H : G D n → ℝ≥0) (φ : Mx D V.rank n → ℂ) (T : Mx D n n) (g : G D n)
    (β : HermE D n) (val : ℂ) : Prop :=
  ∃ (d : ℕ) (bs : Module.Basis (Fin d) D.host.F D.host.E) (θG : D.what₂.Tau → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (lG : D.what₂.Tau → ℝ) (εG : D.what₂.Tau → Fin V.rank → Bool) (frG : D.what₂.Tau → GL (Fin V.rank) ℂ)
    (gG : D.what₂.Tau → GL (Fin n) ℂ) (PG : D.what₂.Tau → PositivityTheory.Rg.Sw.PX V.rank n)
    (lamG : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E))
    (L₁ L₂ : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      AddSubgroup (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E))
    (ΦG : (Fin n → Fin V.rank → HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (Φf : (Fin n → Fin V.rank → HeckeCharacterZeroLocus.SiegelWeilU.Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (Φv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      (Fin n → Fin V.rank → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) → ℂ)
    (μG : Measure (Fin n → Fin V.rank → HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F ⊗[D.host.F] D.host.E))
    (νG : Measure (HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig n))
    (ψG : AddChar (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) ℂ),
    PositivityTheory.SiegelWeilFormula.Gen.Dat D.sp.cm.sig (HSpace.gram V) β.1 bs ψG θG lG εG frG gG PG lamG L₁ L₂ ΦG Φf Φv μG νG ∧
    ∃ C : ℂ, (∃ t : ℝ, ∀ z : ℂ, t < z.re →
      Integrable (PositivityTheory.SiegelWeilFormula.Gen.whI (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψG μG ΦG
        (PositivityTheory.SiegelWeilFormula.Gen.nuA θG gG lamG L₁ L₂) (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F))) z) νG ∧
      whitT ψ V μ lam nb w H φ T g z = C * ∫ b, PositivityTheory.SiegelWeilFormula.Gen.whI (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψG μG ΦG
        (PositivityTheory.SiegelWeilFormula.Gen.nuA θG gG lamG L₁ L₂) (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F))) z b ∂νG) ∧
    ∀ μH 𝓕, HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH D.host.F D.host.E D.sp.cm.sig V.rank (HSpace.gram V) μH →
      HeckeCharacterZeroLocus.SiegelWeilU.IsFDH D.host.F D.host.E D.sp.cm.sig V.rank (HSpace.gram V) μH 𝓕 →
      val = C * HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕
        (HeckeCharacterZeroLocus.SiegelWeilU.thetaS D.host.F D.host.E D.sp.cm.sig V.rank (HSpace.gram V) ΦG
          {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig (HSpace.gram V) X = β.1})

def DictKA : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n), CoefData nb lam 𝓖 →
  ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ (β : HermE D n), β.1.det ≠ 0 →
  ∀ a : GL (Fin n) (AE D), ∀ k ∈ K D n,
    ∃ (N : ℕ) (φs : Fin N → Mx D V.rank n → ℂ) (vals : Fin N → ℂ),
      (∃ t : ℝ, ∀ z : ℂ, t < z.re →
        whitT ψ V μ lam nb w H (ω k Φ).1 (adj a.1 * β.1.map (incA D) * a.1) k z =
          ∑ j, whitT ψ V μ lam nb w H (φs j) (adj a.1 * β.1.map (incA D) * a.1) k z) ∧
      npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n) *
          IfrB V ν (fun x => (ω k Φ).1 (HMul.hMul x a.1)) β = ∑ j, vals j ∧
      ∀ j, MatchGenA ψ V μ lam nb w H (φs j) (adj a.1 * β.1.map (incA D) * a.1) k β (vals j)

def WhitKAOfGen : Prop := PositivityTheory.SiegelWeilFormula.Gen.WhitGen → DictKA → WhitKA

end PositivityTheory.PfSWUS

end
