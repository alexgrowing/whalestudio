import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThFEqIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftEqMultiplePrincipalLevelClassSumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumPrincipalLevelEqConstMulClassSumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockReadingTranslatedFormMemComplexFormsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.LiftClassSum

theorem exists_thetaLift_eq_classSum : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ y : (X.R.HV j t).H,
    (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y h) →
    ∃ F ∈ (Y.Z.ρ.B i j b).formsC (Y.Z.ρ.tw i b 0 ∅ 1),
      X.R.thF j t y (X.geo.v₀ j _) = (Y.Z.ρ.B i j b).classSum (X.R.ωP j t) (Y.Z.ρ.tw i b 0 ∅ 1) (Y.Z.ρ.rep i j b (Y.Z.ρ.tw i b 0 ∅ 1)) F := by
  classical
  intro D X E Y i j b t hxi hQ y hy
  obtain ⟨u, hu⟩ := GlobalTheory.LiftClassSum.exists_low D X E Y j
  obtain ⟨m, h₀, c, z, hh₀, hz, hP⟩ := GlobalTheory.T.thetaLift_eq_multiple_principalLevel_classSum D X E Y i j b t hxi hQ y u
  have hB : (Y.Z.ρ.B i j b).Good := Y.Z.good.base i j b
  have hq : (Y.Z.ρ.tw i b 0 ∅ 1).Q = ∅ := half_empty _
  have hc : (Y.Z.ρ.tw i b 0 ∅ 1).chi = 1 := charOf_one _ _
  have hgood : ∀ τ : Twist D Circle, τ.Q = ∅ → τ.chi = 1 → τ.Good := by
    rintro ⟨Q0, c0, r0⟩ hq0 hc0
    dsimp only at hq0 hc0
    subst hq0 hc0
    have h1 := Twist.triv_good (D := D) (A := Circle) (Q := ∅) splitSet_empty
    exact ⟨h1.isOpen, h1.rat, h1.real, h1.split, h1.unram, fun _ h => absurd h (Finset.notMem_empty _)⟩
  have hψ : (Y.Z.ρ.tw i b 0 ∅ 1).Good := hgood _ hq hc
  have hA : (Y.Z.ρ.B i j b).admitted (Y.Z.ρ.tw i b 0 ∅ 1).Q := by rw [hq]; exact Base.admissible_empty_of_good hB
  have hBase : GlobalTheory.ConjTwist.BaseOf X.R.toRealDat j (Y.Z.ρ.B i j b) :=
    GlobalTheory.PinBase.baseOf_of_pin D X Y.Z.ρ Y.Z.good Y.Z.pin i j b
  have htup : GlobalTheory.ConjTwist.IsTupOf X.R.toRealDat (Y.Z.ρ.B i j b) (Y.Z.ρ.tw i b 0 ∅ 1) t :=
    ⟨by rw [hxi, hc, mul_one], by rw [hQ, hq, Finset.union_empty]⟩
  have hW : (Y.Z.ρ.B i j b).IsWeil (Y.Z.ρ.tw i b 0 ∅ 1).chi (X.R.ωP j t) := hBase.isWeil X.char.thP.ωP htup
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.classSum_principalLevel_eq_const_mul_classSum D _ _ (Y.Z.ρ.B i j b) hB (D.sp.V_sig _) _ hψ hA _ hW m h₀ hh₀ _
    (Y.Z.ρ.rep i j b (Y.Z.ρ.tw i b 0 ∅ 1)) (Y.Z.good.classes i j b _ hψ hA)
  have hF := GlobalTheory.T.fockReading_translatedForm_mem_complexForms D X E Y i j b t hxi hQ y hy u hu z hz
  refine ⟨(c * κ) • (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * z))), Submodule.smul_mem _ _ hF, ?_⟩
  refine (congrArg (fun v => X.R.thF j t y v) hu.symm).trans (hP.trans ?_)
  exact (congrArg (c • ·) (hκ _ hF)).trans ((smul_smul c κ _).trans (LinearMap.map_smul _ _ _).symm)

end GlobalTheory.LiftClassSum

end
