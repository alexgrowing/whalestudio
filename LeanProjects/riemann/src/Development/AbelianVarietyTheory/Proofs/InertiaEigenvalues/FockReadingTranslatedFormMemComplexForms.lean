import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThFEqIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseOfOfPin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOfLowSmoothLines
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000
noncomputable section

namespace GlobalTheory.FockReadForms

theorem fockRead_mem_formsC : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ y : (X.R.HV j t).H,
    (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y h) →
    ∀ (u : ∀ ρ, lowT (X.R.MW j (sg0 D X.A3.A)) ρ),
      (fun ρ => (u ρ : ↥((X.R.MW j (sg0 D X.A3.A)).sm ρ))) = X.geo.v₀ j (sg0 D X.A3.A) →
    ∀ (z : Bridge.Gf (Vc D j)), z ∈ Subgroup.center (Bridge.Gf (Vc D j)) →
    (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * z))) ∈ (Y.Z.ρ.B i j b).formsC (Y.Z.ρ.tw i b 0 ∅ 1) := by
  intro D X E Y i j b t hxi hQ y hlaw u hu z hz
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 :=
    ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.chain, X.char.thP⟩
  have hBo : GlobalTheory.ConjTwist.BaseOf X.R.toRealDat j (Y.Z.ρ.B i j b) :=
    GlobalTheory.PinBase.baseOf_of_pin D X Y.Z.ρ Y.Z.good Y.Z.pin i j b
  have hG : (Y.Z.ρ.B i j b).Good := Y.Z.good.base i j b
  have htup : GlobalTheory.ConjTwist.IsTupOf X.R.toRealDat (Y.Z.ρ.B i j b) (Twist.triv Circle ∅) t := by
    classical
    exact ⟨by rw [hxi]; exact (mul_one _).symm, by rw [hQ]; exact (Finset.union_empty _).symm⟩
  have hact := (GlobalTheory.CoefActIo.act_ioP hC hG hBo (Twist.triv_good splitSet_empty) htup).2
  have hio : Formalism.IndefR.FWT.IoExt X.R.toRealDat :=
    GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP
  have hval : ∀ w, X.R.ioP j (PiTensorProduct.tprod ℂ u) w ∈ (Y.Z.ρ.B i j b).valSpace := by
    intro w
    have hcV : (X.R.cV j).Is := hC.models.cV j
    obtain ⟨u', w₀, hu', -, hw⟩ := Formalism.IndefR.FWT.IsChosenExtremalVector.io _ (Y.Z.vec j) hio
    have huu : u' = u := funext fun ρ => Subtype.ext ((hu' ρ).trans (congrFun hu ρ).symm)
    rw [huu] at hw
    have hT := Scale.io_act hC.lev hC.thP hG hBo.ψ hBo.θ hBo.sT hBo.BS hBo.BT hBo.mu0 hBo.eta (PiTensorProduct.tprod ℂ u)
    have hΔ0 := GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) j
    rcases hcV.2.2.2.2 ((harm (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS).comap
        (X.R.ioP j (PiTensorProduct.tprod ℂ u))) (fun h => by
        obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 h
        rw [map_mul, hcV.1 k hk, mul_one]
        rintro _ ⟨w, hw', rfl⟩
        rw [Submodule.mem_comap, hT a ha]
        exact fockGL_mem_harm _ _ _ hw') with h | h
    · have h0 : w₀ ∈ (harm (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS).comap
          (X.R.ioP j (PiTensorProduct.tprod ℂ u)) := by
        rw [Submodule.mem_comap, hw, ← hBo.delta]
        exact delta_mem_harm _ _
      rw [h, Submodule.mem_bot] at h0
      rw [h0, map_zero] at hw
      exact absurd hw.symm hΔ0
    · exact (h ▸ Submodule.mem_top : w ∈ (harm (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS).comap
        (X.R.ioP j (PiTensorProduct.tprod ℂ u)))

  have hx : (X.R.HV j t).e y ∈ Bridge.AdForms (Bridge.ratF (Vc D j)) (X.R.cV j).coef.ρ
      (levEnv _ (X.R.βV j) (X.R.datVt j t)).J (levEnv _ (X.R.βV j) (X.R.datVt j t)).χ :=
    (hC.models.HV j t).2.1.le (LinearMap.mem_range_self _ y)
  rw [Base.mem_formsC]
  refine ⟨fun h => hval _, fun γ h k => ?_⟩
  have hzc := Subgroup.mem_center_iff.1 hz
  have e1 : Bridge.ratF (Vc D j) γ * h * (k : Bridge.Gf (Vc D j)) * z =
      Bridge.ratF (Vc D j) γ * (h * z) * (k : Bridge.Gf (Vc D j)) := by
    simp only [mul_assoc]
    rw [← hzc]
  have h2 : Bridge.ratF (Vc D j) γ * (h * z) * ((1 : (levEnv _ (X.R.βV j) (X.R.datVt j t)).J) : Bridge.Gf (Vc D j)) =
      Bridge.ratF (Vc D j) γ * (h * z) := by
    rw [OneMemClass.coe_one]
    exact mul_one _
  have e2 : (X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z)) =
      (X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z)) :=
    calc (X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z))
        = (X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z) *
            ((1 : (levEnv _ (X.R.βV j) (X.R.datVt j t)).J) : Bridge.Gf (Vc D j))) := congrArg _ h2.symm
      _ = (((levEnv _ (X.R.βV j) (X.R.datVt j t)).χ 1 : ℂˣ) : ℂ) • (X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z)) :=
          hx γ (h * z) 1
      _ = (1 : ℂ) • (X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z)) :=
          congrArg (fun c : ℂ => c • (X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z)))
            (by rw [MonoidHom.map_one, Units.val_one])
      _ = (X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z)) := one_smul ℂ _
  calc X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * h * (k : Bridge.Gf (Vc D j)) * z))
      = X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z) * (k : Bridge.Gf (Vc D j)))) :=
        congrArg (fun g => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y g)) e1
    _ = X.R.ioP j (PiTensorProduct.tprod ℂ u) ((((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) •
          (X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z))) :=
        congrArg (X.R.ioP j (PiTensorProduct.tprod ℂ u)) (hlaw _ k)
    _ = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) •
          X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z))) :=
        map_smul _ _ _
    _ = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) •
          X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z))) :=
        congrArg (fun v => (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • X.R.ioP j (PiTensorProduct.tprod ℂ u) v) e2
    _ = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) •
          (Y.Z.ρ.B i j b).act (γ : GA D (Vc D j)) (X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * z))) :=
        congrArg (fun v => (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • v) (hact _ _ _).symm

end GlobalTheory.FockReadForms

end
